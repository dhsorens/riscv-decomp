/-
  Decomp.Region.Limbs

  A multiprecision integer as a region of 64-bit limbs, and a field element as
  a limb region carrying its own range invariant.

  The default triples give a flat functional view of memory: a region is a byte
  list, and every arithmetic proof over it restates where the bytes are. This
  file is the vocabulary that makes instructions read as operating over an array
  of limbs directly -- `ROADMAP.md` item 11, and issue #27's design.

  ## The layering

  `limbRegionOn valid base ws` is *defined through* `bytesRegionOn`, not as a
  fresh `**`-chain: it is the byte region whose contents are the limbs'
  little-endian payloads (`ws.flatMap dwordBytes`). So the two keystones here
  are the wide-region keystones at byte index `8k`, plus two list lemmas that
  say which window of the flattened list limb `k` occupies:

  * `limbRegionOn_ld_at` -- `LD rd, 8k(rs1)` delivers `ws[k]`, from
    `bytesRegionOn_ld_at` and `limbBytes_window`;
  * `limbRegionOn_sd_at` -- `SD` at `8k` yields `limbRegionOn base (ws.set k v)`,
    from `bytesRegionOn_sd_at` and `limbBytes_setBytes`.

  Nothing here needs `halign` or `hover`, and that is inherited rather than
  arranged: an 8-aligned wide access hits one of the region's own cells exactly,
  so neither keystone carries them (`Region/Wide.lean`'s note). A limb array's
  accesses are 8-aligned by construction, so the alignment side condition is
  discharged by `Nat.dvd_mul_right` and never reaches a caller.

  `limbRegionOn` is an `abbrev` on purpose. `xperm` normalizes at reducible
  transparency only, so behind a `def` it could not see the `**` chain and
  would fail with an atom-count mismatch; as an `abbrev` it unfolds to
  `bytesRegionOn`, which `xperm_hyp` already treats as an atom.

  ## The invariant is in the assertion

  `fieldElemOn valid p base n x` is an existential over the limb list carrying
  `x < p` **inside** it. That is deliberate, and it is what distinguishes a
  field element from an integer that happens to fit: the bound is the invariant
  every arithmetic triple would otherwise restate in its hypotheses, and
  `fieldElemOn valid p base n : Nat → Assertion` is the shape a representation
  relation downstream wants.

  ## What is *not* shown here, and matters

  An existential assertion with no inhabitant is this library's characteristic
  failure -- a true theorem that says nothing -- so `fieldElemOn`'s
  non-vacuity is the thing to get right. What this file proves is the
  *reduction*: `fieldElemOn_of_limbRegion` and `fieldElemOn_natToLimbs` turn a
  limb region at a representable value into a field element, and the round trip
  (`limbsToNat_natToLimbs_of_lt`, `natToLimbs_limbsToNat`) is proved in both
  directions with no machine in sight.

  What it does **not** prove is that `bytesRegionOn` itself has an inhabitant
  at a concrete address, because nothing reachable from a `module` does.
  Upstream's `satWithin_bytesRegion` is stated only for the ZisK cell and lives
  in `RiscvZkvm.Rv64.Logic.MemSat`, a legacy file `Decomp/Upstream.lean`
  deliberately omits; a `module` cannot import it. So the buck stops one layer
  below this file, and it stops there for `anyBytesOn` (`Region/Wide.lean`)
  already. `ROADMAP.md` item 11 records it as the residual.
-/

module

public import Decomp.Region.WideLoad

-- The `#guard`s below *run* `limbsToNat`, `dwordBytes` and `packBytes`, so
-- those need to be importable as code, not only as terms.
meta import RiscvZkvm.Rv64.Logic.ByteOps
meta import RiscvZkvm.Rv64.Logic.MemRegionWriteWide

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

variable {valid : Word → Bool}

/-! ## The abstract value of a limb list -/

/-- A little-endian multiprecision integer as its 64-bit limbs: the head is the
    least significant limb.

    Over `Word.toNat` rather than over bytes, on purpose. Relating a byte
    region to a `Nat` directly would need
    `(packBytes chunk).toNat = Σ bᵢ · 256ⁱ`, a disjointness-of-`|||` argument;
    going through limbs never needs it, because `packBytes (dwordBytes v) = v`
    is an identity on `Word` and the byte level is never unpacked. -/
def limbsToNat : List Word → Nat
  | []      => 0
  | w :: ws => w.toNat + 2 ^ 64 * limbsToNat ws

/-- `x` as `n` little-endian limbs, truncating anything above `2 ^ (64 * n)`. -/
def natToLimbs : Nat → Nat → List Word
  | 0,     _ => []
  | n + 1, x => BitVec.ofNat 64 x :: natToLimbs n (x / 2 ^ 64)

@[simp] theorem limbsToNat_nil : limbsToNat [] = 0 := rfl

@[simp] theorem limbsToNat_cons (w : Word) (ws : List Word) :
    limbsToNat (w :: ws) = w.toNat + 2 ^ 64 * limbsToNat ws := rfl

@[simp] theorem natToLimbs_zero (x : Nat) : natToLimbs 0 x = [] := rfl

@[simp] theorem length_natToLimbs (n x : Nat) : (natToLimbs n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [natToLimbs, List.length_cons, ih]

/-- Every limb list denotes a value below its capacity. So `fieldElemOn` at an
    `n` too small to hold `p` is empty for the large residues, which is a
    property of the layout and not a defect -- a caller picks `n` with
    `p ≤ 2 ^ (64 * n)`. -/
theorem limbsToNat_lt (ws : List Word) : limbsToNat ws < 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      have hw : w.toNat < 2 ^ 64 := w.isLt
      have hsplit : 2 ^ (64 * (ws.length + 1)) = 2 ^ 64 * 2 ^ (64 * ws.length) := by
        rw [show 64 * (ws.length + 1) = 64 + 64 * ws.length from by omega, Nat.pow_add]
      have hstep : 2 ^ 64 * limbsToNat ws + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * ws.length) := by
        rw [show 2 ^ 64 * limbsToNat ws + 2 ^ 64 = 2 ^ 64 * (limbsToNat ws + 1) from by
          rw [Nat.mul_add, Nat.mul_one]]
        exact Nat.mul_le_mul_left _ ih
      rw [List.length_cons, limbsToNat_cons, hsplit]
      omega

/-! ## The round trip -/

/-- **Down and back up.** For a representable `x`, splitting into `n` limbs and
    recombining is the identity. One of the two halves M4's acceptance asks for. -/
theorem limbsToNat_natToLimbs_of_lt {n x : Nat} (hx : x < 2 ^ (64 * n)) :
    limbsToNat (natToLimbs n x) = x := by
  induction n generalizing x with
  | zero =>
      rw [Nat.mul_zero, Nat.pow_zero] at hx
      rw [natToLimbs_zero, limbsToNat_nil]
      omega
  | succ n ih =>
      have hsplit : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
        rw [show 64 * (n + 1) = 64 + 64 * n from by omega, Nat.pow_add]
      have hdiv : x / 2 ^ 64 < 2 ^ (64 * n) := by
        apply Nat.div_lt_of_lt_mul
        rw [← hsplit]; exact hx
      rw [natToLimbs, limbsToNat_cons, ih hdiv, BitVec.toNat_ofNat]
      exact Nat.mod_add_div x (2 ^ 64)

/-- **Up and back down.** Recombining a limb list and re-splitting it at its own
    length is the identity. The other half. -/
theorem natToLimbs_limbsToNat (ws : List Word) :
    natToLimbs ws.length (limbsToNat ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      have hw : w.toNat < 2 ^ 64 := w.isLt
      have hhead : BitVec.ofNat 64 (w.toNat + 2 ^ 64 * limbsToNat ws) = w := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mul_comm, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hw]
      have htail : (w.toNat + 2 ^ 64 * limbsToNat ws) / 2 ^ 64 = limbsToNat ws := by
        rw [Nat.mul_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
          Nat.div_eq_of_lt hw, Nat.zero_add]
      simp only [List.length_cons, limbsToNat_cons, natToLimbs, hhead, htail, ih]

/-! ## The byte-level layout

The three helpers below are the only list surgery this file does. Each splits
the flattened payload at the first limb's eight bytes, because that is the
recursion `List.flatMap` gives and the index arithmetic `8 * k` follows it. -/

/-- Two byte lists agreeing on a prefix and the matching suffix are equal. -/
private theorem eq_of_take_drop_eq {l₁ l₂ : List (BitVec 8)} (n : Nat)
    (ht : l₁.take n = l₂.take n) (hd : l₁.drop n = l₂.drop n) : l₁ = l₂ := by
  rw [← List.take_append_drop n l₁, ← List.take_append_drop n l₂, ht, hd]

private theorem take_append_dwordBytes (v : Word) (t : List (BitVec 8)) :
    (dwordBytes v ++ t).take 8 = dwordBytes v := by
  rw [List.take_append]; simp [dwordBytes]

private theorem drop_append_dwordBytes (v : Word) (t : List (BitVec 8)) :
    (dwordBytes v ++ t).drop 8 = t := by
  rw [List.drop_append]; simp

/-- A full-width overwrite: splicing eight bytes over a limb's own eight bytes
    leaves the payload of the new limb and nothing of the old. -/
private theorem setBytes_dwordBytes_self (w v : Word) :
    setBytes (dwordBytes w) 0 (dwordBytes v) = dwordBytes v := by
  simp [dwordBytes, setBytes]

/-- A limb list's byte payload is eight bytes per limb. -/
@[simp] theorem length_limbBytes (ws : List Word) :
    (ws.flatMap dwordBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [List.flatMap_cons, List.length_append, length_dwordBytes, ih,
        List.length_cons]
      omega

/-- **Which window limb `k` occupies**: the eight bytes at byte index `8k` of
    the flattened list are limb `k`'s payload. This is the load side's list
    lemma, and `bytesRegionOn_ld_at`'s postcondition is stated in exactly this
    shape. -/
theorem limbBytes_window (ws : List Word) (k : Nat) (hk : k < ws.length) :
    ((ws.flatMap dwordBytes).drop (8 * k)).take 8 = dwordBytes ws[k] := by
  induction ws generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
      cases k with
      | zero =>
          rw [List.flatMap_cons, Nat.mul_zero, List.drop_zero,
            take_append_dwordBytes]
          rfl
      | succ k =>
          have hk' : k < ws.length := by simp only [List.length_cons] at hk; omega
          rw [List.flatMap_cons, show 8 * (k + 1) = 8 + 8 * k from by omega,
            List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append]
          simpa using ih k hk'

/-- **The store side's list lemma**: splicing limb `k`'s cell is setting limb
    `k`. `bytesRegionOn_sd_at`'s postcondition is stated in exactly this shape. -/
theorem limbBytes_setBytes (ws : List Word) (v : Word) (k : Nat) :
    setBytes (ws.flatMap dwordBytes) (8 * k) (dwordBytes v)
      = (ws.set k v).flatMap dwordBytes := by
  induction ws generalizing k with
  | nil => simp
  | cons w ws ih =>
      cases k with
      | zero =>
          rw [List.flatMap_cons, List.set_cons_zero, List.flatMap_cons, Nat.mul_zero]
          refine eq_of_take_drop_eq 8 ?_ ?_
          · rw [setBytes_take_of_le _ _ _ _ (by simp), take_append_dwordBytes,
              setBytes_dwordBytes_self, take_append_dwordBytes]
          · rw [setBytes_drop_of_le _ _ _ _ (by simp), drop_append_dwordBytes,
              drop_append_dwordBytes]
      | succ k =>
          rw [List.flatMap_cons, List.set_cons_succ, List.flatMap_cons,
            show 8 * (k + 1) = 8 + 8 * k from by omega]
          refine eq_of_take_drop_eq 8 ?_ ?_
          · rw [setBytes_take_of_ge _ _ _ _ (by omega), take_append_dwordBytes,
              take_append_dwordBytes]
          · rw [setBytes_drop_of_ge _ _ _ _ (by omega), drop_append_dwordBytes,
              drop_append_dwordBytes, Nat.add_sub_cancel_left, ih]

/-- `packBytes` of a limb's own payload is the limb. The one `ByteOps` identity
    the layering needs; `packBytes_readback_setBytes_dword`
    (`Region/Wide.lean`) is its sequenced store-then-load form. -/
theorem packBytes_dwordBytes (v : Word) : packBytes (dwordBytes v) = v := by
  apply eq_of_forall_extractByte
  intro j hj
  rw [extractByte_packBytes_total _ j hj]
  nat_lt_cases j 8 <;> simp [dwordBytes, getByteAt]

/-! ## The limb region -/

/-- `ws` laid out from `base`, one 64-bit limb per cell, little-endian within
    each limb.

    An `abbrev`, so `xperm` can see through it to `bytesRegionOn` -- behind a
    `def` it would fail with an atom-count mismatch. -/
abbrev limbRegionOn (valid : Word → Bool) (base : Word) (ws : List Word) : Assertion :=
  bytesRegionOn valid base (ws.flatMap dwordBytes)

theorem limbRegionOn_pcFree (base : Word) (ws : List Word) :
    (limbRegionOn valid base ws).pcFree :=
  bytesRegionOn_pcFree valid base _

/-! ## The two keystones -/

/-- **`LD rd, 8k(rs1)` reads limb `k`.** The region keystone at byte index
    `8k`, with the window lemma and `packBytes_dwordBytes` collapsing the
    postcondition to the limb itself.

    No alignment or overflow side condition: `8 ∣ 8k` is discharged here, and
    an 8-aligned wide access hits one of the region's own cells exactly. -/
theorem limbRegionOn_ld_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (ws : List Word) (k : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 (8 * k))
    (hk : k < ws.length)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LD rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * k)) = true →
      st.next s = some (execInstrBr s (.LD rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** limbRegionOn valid regionBase ws)
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ ws[k]) ** limbRegionOn valid regionBase ws) := by
  have h := bytesRegionOn_ld_at (st := st) (valid := valid) rd rs1 regionBase ptr vOld
    offset base (ws.flatMap dwordBytes) (8 * k) hrd hptr (Nat.dvd_mul_right 8 k)
    (by rw [length_limbBytes]; omega) hst
  rwa [limbBytes_window ws k hk, packBytes_dwordBytes] at h

/-- **`SD rs2, 8k(rs1)` writes limb `k`.** The postcondition is the limb region
    with limb `k` replaced -- `List.set`, not a byte splice. -/
theorem limbRegionOn_sd_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (ws : List Word) (k : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 (8 * k))
    (hk : k < ws.length)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SD rs1 rs2 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * k)) = true →
      st.next s = some (execInstrBr s (.SD rs1 rs2 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** limbRegionOn valid regionBase ws)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** limbRegionOn valid regionBase (ws.set k v_data)) := by
  have h := bytesRegionOn_sd_at (st := st) (valid := valid) rs1 rs2 regionBase ptr v_data
    offset base (ws.flatMap dwordBytes) (8 * k) hptr (Nat.dvd_mul_right 8 k)
    (by rw [length_limbBytes]; omega) hst
  rwa [limbBytes_setBytes ws v_data k] at h

/-! ## Field elements -/

/-- A field element of `GF(p)` at `base`, as `n` limbs whose value is `x`.

    `x < p` sits **inside** the assertion. That is the point: it is what
    distinguishes a field element from an integer that happens to fit, it is
    the invariant every arithmetic triple would otherwise carry in its
    hypotheses, and it makes `fieldElemOn valid p base n : Nat → Assertion` a
    representation relation rather than a layout. -/
def fieldElemOn (valid : Word → Bool) (p : Nat) (base : Word) (n : Nat) (x : Nat) :
    Assertion :=
  fun h => ∃ ws : List Word, ws.length = n ∧ limbsToNat ws = x ∧ x < p ∧
           limbRegionOn valid base ws h

theorem pcFree_fieldElemOn (p : Nat) (base : Word) (n x : Nat) :
    (fieldElemOn valid p base n x).pcFree := by
  rintro h ⟨ws, _, _, _, hr⟩
  exact limbRegionOn_pcFree base ws h hr

/-! ### Non-vacuity, as far as it goes

The reduction, not the witness: these say a limb region *is* a field element at
a representable value. The remaining step -- that `bytesRegionOn` has an
inhabitant at a concrete address -- is not available from a `module`; see the
file header and `ROADMAP.md` item 11. -/

/-- **Introduction.** A limb region whose value is in range is a field element.
    The mirror of `bytesRegionOn_anyBytes`. -/
theorem fieldElemOn_of_limbRegion {p : Nat} {base : Word} {ws : List Word}
    (hx : limbsToNat ws < p) (h : PartialState)
    (hr : limbRegionOn valid base ws h) :
    fieldElemOn valid p base ws.length (limbsToNat ws) h :=
  ⟨ws, rfl, rfl, hx, hr⟩

/-- **Introduction at a value.** For a representable `x`, `natToLimbs` is the
    witness, so a region holding those limbs is the field element `x`. This is
    the form that shows the existential is not empty for any `x` a caller can
    name. -/
theorem fieldElemOn_natToLimbs {p n x : Nat} {base : Word}
    (hx : x < p) (hrep : x < 2 ^ (64 * n)) (h : PartialState)
    (hr : limbRegionOn valid base (natToLimbs n x) h) :
    fieldElemOn valid p base n x h :=
  ⟨natToLimbs n x, length_natToLimbs n x, limbsToNat_natToLimbs_of_lt hrep, hx, hr⟩

/-- **Elimination.** A field element is a limb region at *some* limb list whose
    value is `x` and which is in range -- what an arithmetic triple destructures
    to get its keystones. -/
theorem limbRegion_of_fieldElemOn {p n x : Nat} {base : Word} {h : PartialState}
    (hf : fieldElemOn valid p base n x h) :
    ∃ ws : List Word, ws.length = n ∧ limbsToNat ws = x ∧ x < p ∧
      limbRegionOn valid base ws h := hf

/-! ### A satisfiable instance

The reduction lemmas above are conditional: they turn a limb region into a
field element. On their own they would leave `fieldElemOn` exactly as
suspicious as `anyBytesOn` is -- an existential nobody has exhibited. So here
is one, built rather than assumed: two limbs at a concrete address, a concrete
modulus, and a partial state that satisfies the assertion.

It is concrete on purpose. The general statement -- every `bytesRegionOn` with
valid, non-wrapping cells is satisfiable -- needs the region's addresses shown
pairwise distinct, which is a `bytesRegionOn`-layer lemma and not a limb one;
upstream has it for the ZisK cell only, in a legacy file a `module` cannot
import. At a concrete base the distinctness is `decide`-able, which is the
whole reason this fits in one file. -/

/-- The two cells the probe owns, and nothing else. -/
def probeValid : Word → Bool := fun a => a == 0x1000 || a == 0x1008

/-- Two limbs at `0x1000`: the value `2 ^ 64 + 5`, little-endian, so the low
    cell holds `5` and the high cell `1`. -/
def probeState : PartialState :=
  (PartialState.singletonMem 0x1000 5).union
    ((PartialState.singletonMem 0x1008 1).union PartialState.empty)

/-- **The probe is a limb region.** Non-vacuity for `limbRegionOn`, exhibited. -/
theorem probe_limbRegionOn :
    limbRegionOn probeValid 0x1000 [(5 : Word), 1] probeState := by
  refine ⟨PartialState.singletonMem 0x1000 5, _, ?_, rfl, ⟨rfl, by decide⟩, ?_⟩
  · refine ⟨fun _ => Or.inl rfl, fun a => ?_, fun _ => Or.inl rfl, Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    cases hb : (a == (0x1000 : Word)) with
    | true =>
        have ha : a = 0x1000 := by simpa using hb
        exact Or.inr (by subst ha; decide)
    | false =>
        refine Or.inl ?_
        simp only [PartialState.singletonMem, hb, Bool.false_eq_true, if_false]
  · refine ⟨PartialState.singletonMem 0x1008 1, PartialState.empty, ?_, rfl,
      ⟨rfl, by decide⟩, rfl⟩
    exact PartialState.Disjoint_empty_right

/-- **The probe is a field element**, at a modulus that leaves room for it.
    This is the statement that says `fieldElemOn` is not empty. -/
theorem probe_fieldElemOn :
    fieldElemOn probeValid (2 ^ 127 - 1) 0x1000 2 (2 ^ 64 + 5) probeState :=
  ⟨[(5 : Word), 1], rfl, by decide, by decide, probe_limbRegionOn⟩

/-- And so the existential is inhabited, which is the form the next caller of
    `fieldElemOn` will want to see. -/
theorem fieldElemOn_nonvacuous :
    ∃ h : PartialState, fieldElemOn probeValid (2 ^ 127 - 1) 0x1000 2 (2 ^ 64 + 5) h :=
  ⟨probeState, probe_fieldElemOn⟩

/-! ## Pinned by evaluation

`limbsToNat` and `natToLimbs` are computable, so the endianness convention and
the round trip are checked by running them rather than by reading them. The
second `#guard` is the one that matters: it fails if the limb order is ever
flipped. -/

-- The head limb is the least significant.
#guard limbsToNat [(1 : Word), 0] == 1
#guard limbsToNat [(0 : Word), 1] == 2 ^ 64
#guard limbsToNat [(0 : Word), 0, 1] == 2 ^ 128
#guard natToLimbs 2 (2 ^ 64 + 5) == [(5 : Word), 1]
#guard limbsToNat (natToLimbs 3 (2 ^ 130 + 7)) == 2 ^ 130 + 7
#guard natToLimbs 2 (limbsToNat [(7 : Word), 9]) == [(7 : Word), 9]
#guard (([(1 : Word), 2].flatMap dwordBytes)).length == 16
#guard packBytes (dwordBytes 0xdeadbeefcafe) == (0xdeadbeefcafe : Word)

end Decomp
