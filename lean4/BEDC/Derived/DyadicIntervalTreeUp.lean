import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalTreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DyadicIntervalTreeCarrier (R D B F M Q NW H C P L : BHist) : Prop :=
  UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory B ∧ UnaryHistory F ∧
    UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory L ∧ Cont R B F ∧ Cont F M Q ∧ Cont Q D NW

theorem DyadicIntervalTreeCarrier_namecert_obligations {R D B F M Q NW H C P L : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      SemanticNameCert
          (fun row : BHist =>
            DyadicIntervalTreeCarrier R D B F M Q NW H C P L ∧ hsame row L ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row D ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨
              hsame row Q ∨ hsame row NW ∨ hsame row L)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R B F ∧ Cont F M Q ∧ Cont Q D NW)
          hsame ∧ UnaryHistory Q ∧ UnaryHistory NW := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet
  have packetCore := packet
  obtain
    ⟨_unaryR, unaryD, _unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      unaryL, routeF, routeQ, routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryNW : UnaryHistory NW :=
    unary_cont_closed unaryQ unaryD routeNW
  have sourceAtL :
      DyadicIntervalTreeCarrier R D B F M Q NW H C P L ∧ hsame L L ∧
        UnaryHistory L :=
    ⟨packetCore, hsame_refl L, unaryL⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            DyadicIntervalTreeCarrier R D B F M Q NW H C P L ∧ hsame row L ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row D ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨
              hsame row Q ∨ hsame row NW ∨ hsame row L)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R B F ∧ Cont F M Q ∧ Cont Q D NW)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro L sourceAtL
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨source.left,
            hsame_trans (hsame_symm sameRows) source.right.left,
            unary_transport source.right.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.right.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, routeF, routeQ, routeNW⟩
  }
  exact ⟨cert, unaryQ, unaryNW⟩

theorem DyadicIntervalTreeFrontierExhaustion {R D B F M Q NW H C P L leafRead : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      hsame leafRead F ->
        SemanticNameCert
            (fun row : BHist => hsame row leafRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row R ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨
                hsame row Q ∨ hsame row leafRead)
            (fun row : BHist => UnaryHistory row ∧ Cont R B F ∧ Cont F M Q)
            hsame ∧ UnaryHistory leafRead ∧ Cont F M Q := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sameLeafRead
  obtain
    ⟨_unaryR, _unaryD, _unaryB, unaryF, _unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, routeF, routeQ, _routeNW⟩ := packet
  have leafReadUnary : UnaryHistory leafRead :=
    unary_transport unaryF (hsame_symm sameLeafRead)
  have sourceLeafRead :
      (fun row : BHist => hsame row leafRead ∧ UnaryHistory row) leafRead := by
    exact ⟨hsame_refl leafRead, leafReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row leafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨
              hsame row Q ∨ hsame row leafRead)
          (fun row : BHist => UnaryHistory row ∧ Cont R B F ∧ Cont F M Q)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leafRead sourceLeafRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeF, routeQ⟩
  }
  exact ⟨cert, leafReadUnary, routeQ⟩

end BEDC.Derived.DyadicIntervalTreeUp
