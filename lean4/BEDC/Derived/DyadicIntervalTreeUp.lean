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

theorem DyadicIntervalTreeCarrier_refinement_induction_surface
    {R D B F M Q NW H C P L branchStep windowRead : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont B F branchStep ->
        Cont branchStep NW windowRead ->
          UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory B ∧ UnaryHistory F ∧
            UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory NW ∧
              UnaryHistory branchStep ∧ UnaryHistory windowRead ∧ Cont R B F ∧
                Cont F M Q ∧ Cont Q D NW ∧ Cont B F branchStep ∧
                  Cont branchStep NW windowRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet branchRoute windowRoute
  obtain
    ⟨unaryR, unaryD, unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, routeF, routeQ, routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryNW : UnaryHistory NW :=
    unary_cont_closed unaryQ unaryD routeNW
  have unaryBranch : UnaryHistory branchStep :=
    unary_cont_closed unaryB unaryF branchRoute
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryBranch unaryNW windowRoute
  exact
    ⟨unaryR, unaryD, unaryB, unaryF, unaryM, unaryQ, unaryNW, unaryBranch,
      unaryWindow, routeF, routeQ, routeNW, branchRoute, windowRoute⟩

theorem DyadicIntervalTreeCarrier_branch_coverage
    {R D B F M Q NW H C P L branchRead containmentRead : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont B F branchRead ->
        Cont branchRead Q containmentRead ->
          UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory Q ∧ UnaryHistory branchRead ∧
            UnaryHistory containmentRead ∧ Cont B F branchRead ∧
              Cont branchRead Q containmentRead ∧ Cont Q D NW := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet branchRoute containmentRoute
  obtain
    ⟨_unaryR, unaryD, unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, _routeF, routeQ, routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryBranch : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryF branchRoute
  have unaryContainment : UnaryHistory containmentRead :=
    unary_cont_closed unaryBranch unaryQ containmentRoute
  exact
    ⟨unaryB, unaryF, unaryQ, unaryBranch, unaryContainment, branchRoute,
      containmentRoute, routeNW⟩

theorem DyadicIntervalTreeCarrier_leaf_locality
    {R D B F M Q NW H C P L branchPrefix leafRead localRead : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont B F branchPrefix ->
        Cont branchPrefix M leafRead ->
          Cont leafRead Q localRead ->
            UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory M ∧ UnaryHistory Q ∧
              UnaryHistory branchPrefix ∧ UnaryHistory leafRead ∧ UnaryHistory localRead ∧
                Cont B F branchPrefix ∧ Cont branchPrefix M leafRead ∧
                  Cont leafRead Q localRead ∧ Cont F M Q := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet branchRoute leafRoute localRoute
  obtain
    ⟨_unaryR, _unaryD, unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, _routeF, routeQ, _routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryBranch : UnaryHistory branchPrefix :=
    unary_cont_closed unaryB unaryF branchRoute
  have unaryLeaf : UnaryHistory leafRead :=
    unary_cont_closed unaryBranch unaryM leafRoute
  have unaryLocal : UnaryHistory localRead :=
    unary_cont_closed unaryLeaf unaryQ localRoute
  exact
    ⟨unaryB, unaryF, unaryM, unaryQ, unaryBranch, unaryLeaf, unaryLocal,
      branchRoute, leafRoute, localRoute, routeQ⟩

theorem DyadicIntervalTreeCarrier_mesh_refinement_functoriality
    {R D B F M Q NW H C P L parentChildRead finalWindow : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont M Q parentChildRead ->
        Cont parentChildRead NW finalWindow ->
          UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory NW ∧
            UnaryHistory parentChildRead ∧ UnaryHistory finalWindow ∧ Cont F M Q ∧
              Cont Q D NW ∧ Cont M Q parentChildRead ∧
                Cont parentChildRead NW finalWindow := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet parentChildRoute finalWindowRoute
  obtain
    ⟨_unaryR, unaryD, _unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, _routeF, routeQ, routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryNW : UnaryHistory NW :=
    unary_cont_closed unaryQ unaryD routeNW
  have unaryParentChild : UnaryHistory parentChildRead :=
    unary_cont_closed unaryM unaryQ parentChildRoute
  have unaryFinalWindow : UnaryHistory finalWindow :=
    unary_cont_closed unaryParentChild unaryNW finalWindowRoute
  exact
    ⟨unaryM, unaryQ, unaryNW, unaryParentChild, unaryFinalWindow, routeQ,
      routeNW, parentChildRoute, finalWindowRoute⟩

theorem DyadicIntervalTreeCarrier_window_exhaustion
    {R D B F M Q NW H C P L branchRead containmentRead frontierRead windowRead :
      BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont B F branchRead ->
        Cont branchRead Q containmentRead ->
          Cont F M frontierRead ->
            Cont containmentRead NW windowRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨
                      hsame row Q ∨ hsame row NW ∨ hsame row branchRead ∨
                        hsame row containmentRead ∨ hsame row frontierRead ∨
                          hsame row windowRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B F branchRead ∧
                      Cont branchRead Q containmentRead ∧ Cont F M frontierRead ∧
                        Cont containmentRead NW windowRead)
                  hsame ∧
                UnaryHistory branchRead ∧ UnaryHistory containmentRead ∧
                  UnaryHistory frontierRead ∧ UnaryHistory windowRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet branchRoute containmentRoute frontierRoute windowRoute
  obtain
    ⟨_unaryR, unaryD, unaryB, unaryF, unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, _routeF, routeQ, routeNW⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryF unaryM routeQ
  have unaryNW : UnaryHistory NW :=
    unary_cont_closed unaryQ unaryD routeNW
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryF branchRoute
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed branchUnary unaryQ containmentRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed unaryF unaryM frontierRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed containmentUnary unaryNW windowRoute
  have sourceWindow :
      (fun row : BHist => hsame row windowRead ∧ UnaryHistory row) windowRead := by
    exact ⟨hsame_refl windowRead, windowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row B ∨ hsame row F ∨ hsame row M ∨ hsame row Q ∨
              hsame row NW ∨ hsame row branchRead ∨ hsame row containmentRead ∨
                hsame row frontierRead ∨ hsame row windowRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B F branchRead ∧
              Cont branchRead Q containmentRead ∧ Cont F M frontierRead ∧
                Cont containmentRead NW windowRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro windowRead sourceWindow
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, branchRoute, containmentRoute, frontierRoute, windowRoute⟩
  }
  exact ⟨cert, branchUnary, containmentUnary, frontierUnary, windowUnary⟩

theorem DyadicIntervalTreeCarrier_branch_ledger_depth_bound
    {R D B F M Q NW H C P L branchDepth frontierStep : BHist} :
    DyadicIntervalTreeCarrier R D B F M Q NW H C P L ->
      Cont B D branchDepth ->
        Cont branchDepth F frontierStep ->
          UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory F ∧
            UnaryHistory branchDepth ∧ UnaryHistory frontierStep ∧
              Cont B D branchDepth ∧ Cont branchDepth F frontierStep ∧ Cont Q D NW := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet branchDepthRoute frontierStepRoute
  obtain
    ⟨_unaryR, unaryD, unaryB, unaryF, _unaryM, _unaryH, _unaryC, _unaryP,
      _unaryL, _routeF, _routeQ, routeNW⟩ := packet
  have unaryBranchDepth : UnaryHistory branchDepth :=
    unary_cont_closed unaryB unaryD branchDepthRoute
  have unaryFrontierStep : UnaryHistory frontierStep :=
    unary_cont_closed unaryBranchDepth unaryF frontierStepRoute
  exact
    ⟨unaryB, unaryD, unaryF, unaryBranchDepth, unaryFrontierStep,
      branchDepthRoute, frontierStepRoute, routeNW⟩

end BEDC.Derived.DyadicIntervalTreeUp
