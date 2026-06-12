import BEDC.Derived.BishopRegularCauchyCompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionTailDiameterControl [AskSetup] [PackageSetup]
    {E S R D W H C P N tailBudget streamRead regularRead endpointRead transportRead
      replayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier E S R D W H C P N bundle pkg ->
      Cont D W tailBudget ->
        Cont tailBudget S streamRead ->
          Cont streamRead R regularRead ->
            Cont regularRead E endpointRead ->
              Cont endpointRead H transportRead ->
                Cont transportRead C replayRead ->
                  Cont replayRead N sealRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row D ∨ hsame row W ∨ hsame row S ∨ hsame row R ∨
                                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                                  hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont D W tailBudget ∧
                                Cont tailBudget S streamRead ∧
                                  Cont streamRead R regularRead ∧
                                    Cont regularRead E endpointRead ∧
                                      Cont endpointRead H transportRead ∧
                                        Cont transportRead C replayRead ∧
                                          Cont replayRead N sealRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier tailRoute streamRoute regularRoute endpointRoute transportRoute replayRoute
    sealRoute provenancePkg localNamePkg
  obtain ⟨eUnary, sUnary, rUnary, dUnary, wUnary, hUnary, cUnary, _pUnary, nUnary,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have tailUnary : UnaryHistory tailBudget :=
    unary_cont_closed dUnary wUnary tailRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed tailUnary sUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed regularUnary eUnary endpointRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed endpointUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed replayUnary nUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W tailBudget ∧ Cont tailBudget S streamRead ∧
              Cont streamRead R regularRead ∧ Cont regularRead E endpointRead ∧
                Cont endpointRead H transportRead ∧ Cont transportRead C replayRead ∧
                  Cont replayRead N sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, streamRoute, regularRoute, endpointRoute, transportRoute,
          replayRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
