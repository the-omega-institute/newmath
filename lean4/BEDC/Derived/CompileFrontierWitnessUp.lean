import BEDC.Derived.CompileFrontierWitnessUp.TasteGate

namespace BEDC.Derived.CompileFrontierWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompileFrontierWitness_nonchoice_boundary [AskSetup] [PackageSetup]
    {F T S A B H C P N auditRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompileFrontierWitnessCarrier F T S A B H C P N bundle pkg ->
      Cont S A auditRead ->
        Cont auditRead B boundaryRead ->
          PkgSig bundle N pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row T ∨ hsame row S ∨ hsame row A ∨
                    hsame row B ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S A auditRead ∧ Cont auditRead B boundaryRead ∧
                    PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory boundaryRead ∧
                hsame auditRead (append S A) ∧ hsame boundaryRead (append auditRead B) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: CompileFrontierWitnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier auditRoute boundaryRoute namePkg
  obtain ⟨_fUnary, _tUnary, sUnary, aUnary, bUnary, _hUnary, _cUnary, _pUnary,
    nUnary, provenancePkg, _storedNamePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed sUnary aUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary bUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row T ∨ hsame row S ∨ hsame row A ∨
              hsame row B ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S A auditRead ∧ Cont auditRead B boundaryRead ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRoute, boundaryRoute, namePkg⟩
  }
  exact
    ⟨cert, auditReadUnary, boundaryReadUnary, auditRoute, boundaryRoute, provenancePkg,
      namePkg⟩

theorem CompileFrontierWitness_boundary_exactness [AskSetup] [PackageSetup]
    {F T S A B H C P N auditRead boundaryRead exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompileFrontierWitnessCarrier F T S A B H C P N bundle pkg ->
      Cont S A auditRead ->
        Cont auditRead B boundaryRead ->
          Cont boundaryRead C exitRead ->
            UnaryHistory boundaryRead ∧ hsame boundaryRead (append auditRead B) ∧
              UnaryHistory exitRead ∧ hsame exitRead (append boundaryRead C) ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: CompileFrontierWitnessCarrier BHist Cont PkgSig hsame
  intro carrier auditRoute boundaryRoute exitRoute
  obtain ⟨_fUnary, _tUnary, sUnary, aUnary, bUnary, _hUnary, cUnary, _pUnary,
    _nUnary, provenancePkg, namePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed sUnary aUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary bUnary boundaryRoute
  have exitReadUnary : UnaryHistory exitRead :=
    unary_cont_closed boundaryReadUnary cUnary exitRoute
  exact
    ⟨boundaryReadUnary, boundaryRoute, exitReadUnary, exitRoute, provenancePkg, namePkg⟩

theorem CompileFrontierWitness_consumer_nonescape [AskSetup] [PackageSetup]
    {F T S A B H C P N auditRead boundaryRead cellularRead obstructionRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompileFrontierWitnessCarrier F T S A B H C P N bundle pkg ->
      Cont S A auditRead ->
        Cont auditRead B boundaryRead ->
          Cont boundaryRead P cellularRead ->
            Cont cellularRead N obstructionRead ->
              Cont obstructionRead C consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory cellularRead ∧ UnaryHistory obstructionRead ∧
                    UnaryHistory consumerRead ∧ hsame cellularRead (append boundaryRead P) ∧
                      hsame obstructionRead (append cellularRead N) ∧
                        hsame consumerRead (append obstructionRead C) ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                            PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: CompileFrontierWitnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier auditRoute boundaryRoute cellularRoute obstructionRoute consumerRoute consumerPkg
  obtain ⟨_fUnary, _tUnary, sUnary, aUnary, bUnary, _hUnary, cUnary, pUnary,
    nUnary, provenancePkg, namePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed sUnary aUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary bUnary boundaryRoute
  have cellularReadUnary : UnaryHistory cellularRead :=
    unary_cont_closed boundaryReadUnary pUnary cellularRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed cellularReadUnary nUnary obstructionRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed obstructionReadUnary cUnary consumerRoute
  exact
    ⟨cellularReadUnary, obstructionReadUnary, consumerReadUnary, cellularRoute,
      obstructionRoute, consumerRoute, provenancePkg, namePkg, consumerPkg⟩

end BEDC.Derived.CompileFrontierWitnessUp
