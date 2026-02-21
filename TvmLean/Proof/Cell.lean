import TvmLean.Model

namespace TvmLean

@[simp] theorem builder_empty_bits :
    Builder.empty.bits = #[] := by
  rfl

@[simp] theorem builder_empty_refs :
    Builder.empty.refs = #[] := by
  rfl

@[simp] theorem builder_storeBits_bits (b : Builder) (bs : BitString) :
    (b.storeBits bs).bits = b.bits ++ bs := by
  rfl

@[simp] theorem builder_storeBits_refs (b : Builder) (bs : BitString) :
    (b.storeBits bs).refs = b.refs := by
  rfl

@[simp] theorem builder_storeBits_empty (b : Builder) :
    b.storeBits #[] = b := by
  cases b
  simp [Builder.storeBits]

@[simp] theorem builder_storeBits_storeBits (b : Builder) (bs1 bs2 : BitString) :
    (b.storeBits bs1).storeBits bs2 = b.storeBits (bs1 ++ bs2) := by
  cases b
  simp [Builder.storeBits, Array.append_assoc]

@[simp] theorem builder_finalize_bits (b : Builder) :
    b.finalize.bits = b.bits := by
  rfl

@[simp] theorem builder_finalize_refs (b : Builder) :
    b.finalize.refs = b.refs := by
  rfl

@[simp] theorem builder_finalize_special (b : Builder) :
    b.finalize.special = false := by
  simp [Builder.finalize, Cell.mkOrdinary]

@[simp] theorem builder_finalize_empty :
    Builder.empty.finalize = Cell.empty := by
  rfl

theorem builder_storeBits_finalize (b : Builder) (bs : BitString) :
    (b.storeBits bs).finalize = Cell.mkOrdinary (b.bits ++ bs) b.refs := by
  rfl

theorem builder_storeBits_storeBits_finalize (b : Builder) (bs1 bs2 : BitString) :
    ((b.storeBits bs1).storeBits bs2).finalize = (b.storeBits (bs1 ++ bs2)).finalize := by
  simp

theorem builder_storeBitsChecked_of_canExtendBy (b : Builder) (bs : BitString)
    (h : b.canExtendBy bs.size = true) :
    builderStoreBitsChecked b bs = .ok (b.storeBits bs) := by
  unfold builderStoreBitsChecked
  rw [h]
  rfl

theorem builder_storeBitsChecked_of_not_canExtendBy (b : Builder) (bs : BitString)
    (h : b.canExtendBy bs.size = false) :
    builderStoreBitsChecked b bs = .error .cellOv := by
  unfold builderStoreBitsChecked
  rw [h]
  rfl

theorem builder_storeRefChecked_of_canExtendBy (b : Builder) (c : Cell)
    (h : b.canExtendBy 0 1 = true) :
    builderStoreRefChecked b c = .ok { b with refs := b.refs.push c } := by
  unfold builderStoreRefChecked
  rw [h]
  rfl

theorem builder_storeRefChecked_of_not_canExtendBy (b : Builder) (c : Cell)
    (h : b.canExtendBy 0 1 = false) :
    builderStoreRefChecked b c = .error .cellOv := by
  unfold builderStoreRefChecked
  rw [h]
  rfl

theorem builder_appendCellChecked_of_canExtendBy (b : Builder) (c : Cell)
    (h : b.canExtendBy c.bits.size c.refs.size = true) :
    builderAppendCellChecked b c = .ok { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs } := by
  unfold builderAppendCellChecked
  rw [h]
  rfl

theorem builder_appendCellChecked_of_not_canExtendBy (b : Builder) (c : Cell)
    (h : b.canExtendBy c.bits.size c.refs.size = false) :
    builderAppendCellChecked b c = .error .cellOv := by
  unfold builderAppendCellChecked
  rw [h]
  rfl

theorem cell_depthLe_succ_of_refs_empty (c : Cell) (limit : Nat) (h : c.refs = #[]) :
    c.depthLe (Nat.succ limit) = true := by
  simp [Cell.depthLe, h]

@[simp] theorem cell_empty_depthLe_succ (limit : Nat) :
    Cell.empty.depthLe (Nat.succ limit) = true := by
  simpa using cell_depthLe_succ_of_refs_empty (c := Cell.empty) (limit := limit) rfl

@[simp] theorem cell_empty_depthLe_one :
    Cell.empty.depthLe 1 = true := by
  exact cell_empty_depthLe_succ 0

@[simp] theorem slice_ofCell_bitPos (c : Cell) :
    (Slice.ofCell c).bitPos = 0 := by
  rfl

@[simp] theorem slice_ofCell_refPos (c : Cell) :
    (Slice.ofCell c).refPos = 0 := by
  rfl

@[simp] theorem slice_ofCell_bitsRemaining (c : Cell) :
    (Slice.ofCell c).bitsRemaining = c.bits.size := by
  simp [Slice.bitsRemaining, Slice.ofCell]

@[simp] theorem slice_ofCell_refsRemaining (c : Cell) :
    (Slice.ofCell c).refsRemaining = c.refs.size := by
  simp [Slice.refsRemaining, Slice.ofCell]

@[simp] theorem slice_ofCell_toCellRemaining (c : Cell) :
    (Slice.ofCell c).toCellRemaining = Cell.mkOrdinary c.bits c.refs := by
  simp [Slice.toCellRemaining, Slice.ofCell]

@[simp] theorem slice_ofCell_haveBits (c : Cell) (n : Nat) :
    (Slice.ofCell c).haveBits n = decide (n ≤ c.bits.size) := by
  simp [Slice.haveBits, Slice.ofCell]

@[simp] theorem slice_ofCell_haveRefs (c : Cell) (n : Nat) :
    (Slice.ofCell c).haveRefs n = decide (n ≤ c.refs.size) := by
  simp [Slice.haveRefs, Slice.ofCell]

@[simp] theorem slice_ofCell_readBits (c : Cell) (n : Nat) :
    (Slice.ofCell c).readBits n = c.bits.extract 0 n := by
  simp [Slice.readBits, Slice.ofCell]

@[simp] theorem slice_advanceBits_zero (s : Slice) :
    s.advanceBits 0 = s := by
  cases s
  simp [Slice.advanceBits]

@[simp] theorem slice_advanceBits_cell (s : Slice) (n : Nat) :
    (s.advanceBits n).cell = s.cell := by
  cases s
  rfl

@[simp] theorem slice_advanceBits_bitPos (s : Slice) (n : Nat) :
    (s.advanceBits n).bitPos = s.bitPos + n := by
  cases s
  rfl

@[simp] theorem slice_advanceBits_refPos (s : Slice) (n : Nat) :
    (s.advanceBits n).refPos = s.refPos := by
  cases s
  rfl

@[simp] theorem slice_advanceBits_refsRemaining (s : Slice) (n : Nat) :
    (s.advanceBits n).refsRemaining = s.refsRemaining := by
  cases s
  simp [Slice.advanceBits, Slice.refsRemaining]

@[simp] theorem slice_advanceBits_haveRefs (s : Slice) (n m : Nat) :
    (s.advanceBits n).haveRefs m = s.haveRefs m := by
  cases s
  simp [Slice.advanceBits, Slice.haveRefs]

@[simp] theorem slice_advanceBits_add (s : Slice) (n m : Nat) :
    (s.advanceBits n).advanceBits m = s.advanceBits (n + m) := by
  cases s
  simp [Slice.advanceBits, Nat.add_assoc]

theorem slice_takeBitsAsNatCellUnd_of_haveBits (s : Slice) (n : Nat)
    (h : s.haveBits n = true) :
    s.takeBitsAsNatCellUnd n = .ok (bitsToNat (s.readBits n), s.advanceBits n) := by
  unfold Slice.takeBitsAsNatCellUnd
  rw [h]
  rfl

theorem slice_takeBitsAsNatCellUnd_of_not_haveBits (s : Slice) (n : Nat)
    (h : s.haveBits n = false) :
    s.takeBitsAsNatCellUnd n = .error .cellUnd := by
  unfold Slice.takeBitsAsNatCellUnd
  rw [h]
  rfl

theorem slice_takeRefCell_of_haveRefs (s : Slice) (h : s.haveRefs 1 = true) :
    s.takeRefCell = .ok (s.cell.refs[s.refPos]!, { s with refPos := s.refPos + 1 }) := by
  unfold Slice.takeRefCell
  rw [h]
  rfl

theorem slice_takeRefCell_of_not_haveRefs (s : Slice) (h : s.haveRefs 1 = false) :
    s.takeRefCell = .error .cellUnd := by
  unfold Slice.takeRefCell
  rw [h]
  rfl

theorem slice_ofCell_takeBitsAsNatCellUnd_roundtrip (c : Cell) (n : Nat)
    (hBits : n ≤ c.bits.size) :
    (Slice.ofCell c).takeBitsAsNatCellUnd n =
      .ok (bitsToNat (c.bits.extract 0 n), { cell := c, bitPos := n, refPos := 0 }) := by
  simpa [Slice.readBits, Slice.ofCell, Slice.advanceBits] using
    slice_takeBitsAsNatCellUnd_of_haveBits
      (s := Slice.ofCell c)
      (n := n)
      (by simp [Slice.haveBits, Slice.ofCell, hBits])

theorem slice_ofCell_takeRefCell_roundtrip (c : Cell) (hRef : 1 ≤ c.refs.size) :
    (Slice.ofCell c).takeRefCell = .ok (c.refs[0]!, { cell := c, bitPos := 0, refPos := 1 }) := by
  simpa [Slice.ofCell] using
    slice_takeRefCell_of_haveRefs
      (s := Slice.ofCell c)
      (by simp [Slice.haveRefs, Slice.ofCell, hRef])

theorem slice_ofCell_takeBitsAsNatCellUnd_takeRefCell_roundtrip (c : Cell) (n : Nat)
    (hBits : n ≤ c.bits.size) (hRef : 1 ≤ c.refs.size) :
    (do
      let (x, s1) ← (Slice.ofCell c).takeBitsAsNatCellUnd n
      let (r, s2) ← s1.takeRefCell
      pure (x, r, s2))
    = .ok (bitsToNat (c.bits.extract 0 n), c.refs[0]!, { cell := c, bitPos := n, refPos := 1 }) := by
  unfold Slice.takeBitsAsNatCellUnd Slice.takeRefCell
  simp [Slice.haveBits, Slice.haveRefs, Slice.readBits, Slice.ofCell, Slice.advanceBits, hBits, hRef]
  rfl

theorem encodeDecode_storeBitsChecked_storeRefChecked_takeBits_takeRef
    (bs : BitString) (ref : Cell) (n : Nat)
    (hCap : bs.size ≤ 1023) (hTake : n ≤ bs.size) :
    (do
      let b1 ← builderStoreBitsChecked Builder.empty bs
      let b2 ← builderStoreRefChecked b1 ref
      let s := Slice.ofCell b2.finalize
      let (x, s1) ← s.takeBitsAsNatCellUnd n
      let (r, s2) ← s1.takeRefCell
      pure (x, r, s2))
    = .ok (bitsToNat (bs.extract 0 n), ref,
      { cell := Cell.mkOrdinary bs #[ref], bitPos := n, refPos := 1 }) := by
  have hCanBits : Builder.empty.canExtendBy bs.size = true := by
    simp [Builder.canExtendBy, Builder.empty, hCap]
  have hCanRef : (Builder.empty.storeBits bs).canExtendBy 0 1 = true := by
    simp [Builder.canExtendBy, Builder.empty, Builder.storeBits, hCap]
  rw [builder_storeBitsChecked_of_canExtendBy (b := Builder.empty) (bs := bs) hCanBits]
  change
    (do
      let b2 ← builderStoreRefChecked (Builder.empty.storeBits bs) ref
      let s := Slice.ofCell b2.finalize
      let (x, s1) ← s.takeBitsAsNatCellUnd n
      let (r, s2) ← s1.takeRefCell
      pure (x, r, s2))
    = .ok (bitsToNat (bs.extract 0 n), ref,
      { cell := Cell.mkOrdinary bs #[ref], bitPos := n, refPos := 1 })
  rw [builder_storeRefChecked_of_canExtendBy (b := Builder.empty.storeBits bs) (c := ref) hCanRef]
  simpa [Builder.empty, Builder.storeBits, Builder.finalize] using
    slice_ofCell_takeBitsAsNatCellUnd_takeRefCell_roundtrip
      (c := Cell.mkOrdinary bs #[ref])
      (n := n)
      (hBits := by simpa using hTake)
      (hRef := by simp [Cell.mkOrdinary])

theorem slice_storeBits32_takeBitsAsNat_roundtrip (bs : BitString) (hSize : bs.size = 32) :
    let s := Slice.ofCell ((Builder.empty.storeBits bs).finalize)
    s.takeBitsAsNatCellUnd 32 = .ok (bitsToNat (s.readBits 32), s.advanceBits 32) := by
  intro s
  subst s
  exact slice_takeBitsAsNatCellUnd_of_haveBits
    (s := Slice.ofCell ((Builder.empty.storeBits bs).finalize))
    (n := 32)
    (by
      simp [Slice.haveBits, Slice.ofCell, hSize])

end TvmLean
