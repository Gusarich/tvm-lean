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

@[simp] theorem slice_advanceBits_zero (s : Slice) :
    s.advanceBits 0 = s := by
  cases s
  simp [Slice.advanceBits]

@[simp] theorem slice_advanceBits_add (s : Slice) (n m : Nat) :
    (s.advanceBits n).advanceBits m = s.advanceBits (n + m) := by
  cases s
  simp [Slice.advanceBits, Nat.add_assoc]

end TvmLean
