import BEDC.Derived.CalculusUp.RootUnblockFiniteSumHandoff

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootUnblockRiemannEndpointReadback [AskSetup] [PackageSetup]
    {integralRow endpointRow readbackRow toleranceRow realSeal transport replay provenance
      localName endpointRead readbackRead toleranceRead sealRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory integralRow ->
      UnaryHistory endpointRow ->
        UnaryHistory readbackRow ->
          UnaryHistory toleranceRow ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont integralRow endpointRow endpointRead ->
                    Cont endpointRead readbackRow readbackRead ->
                      Cont readbackRead toleranceRow toleranceRead ->
                        Cont toleranceRead realSeal sealRead ->
                          Cont transport replay structuralRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row integralRow ∨ hsame row endpointRow ∨
                                        hsame row readbackRow ∨ hsame row toleranceRow ∨
                                          hsame row realSeal ∨ hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont integralRow endpointRow endpointRead ∧
                                          Cont endpointRead readbackRow readbackRead ∧
                                            Cont readbackRead toleranceRow toleranceRead ∧
                                              Cont toleranceRead realSeal sealRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory endpointRead ∧
                                    UnaryHistory readbackRead ∧
                                      UnaryHistory toleranceRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro integralUnary endpointUnary readbackUnary toleranceUnary realUnary transportUnary
    replayUnary endpointRoute readbackRoute toleranceRoute sealRoute structuralRoute provenancePkg
    localNamePkg
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed integralUnary endpointUnary endpointRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed endpointReadUnary readbackUnary readbackRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackReadUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary realUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        exact
          ⟨source.right, endpointRoute, readbackRoute, toleranceRoute, sealRoute,
            provenancePkg, localNamePkg⟩
    }
  · exact
      ⟨endpointReadUnary, readbackReadUnary, toleranceReadUnary, sealReadUnary,
        structuralReadUnary⟩

end BEDC.Derived.CalculusUp
