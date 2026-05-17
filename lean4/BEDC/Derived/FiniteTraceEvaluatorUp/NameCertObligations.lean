import BEDC.Derived.FiniteTraceEvaluatorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteTraceEvaluatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteTraceEvaluatorCarrier [AskSetup] [PackageSetup]
    (input trace accepted validation transport route provenance localRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory trace ∧ UnaryHistory accepted ∧
    UnaryHistory validation ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localRow ∧ Cont input trace route ∧
        Cont route accepted localRow ∧ Cont accepted validation provenance ∧
          hsame transport (append input accepted) ∧ PkgSig bundle provenance pkg

theorem FiniteTraceEvaluatorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {input trace accepted validation transport route provenance localRow traceRead
      acceptedRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTraceEvaluatorCarrier input trace accepted validation transport route provenance
        localRow bundle pkg ->
      Cont input trace traceRead ->
        Cont traceRead accepted acceptedRead ->
          Cont accepted validation boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    FiniteTraceEvaluatorCarrier input trace accepted validation transport route
                      provenance localRow bundle pkg ∧ hsame row localRow)
                  (fun row : BHist => hsame row acceptedRead ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                      hsame row localRow)
                  hsame ∧
                UnaryHistory traceRead ∧ UnaryHistory acceptedRead ∧
                  UnaryHistory boundaryRead ∧ Cont input trace traceRead ∧
                    Cont traceRead accepted acceptedRead ∧
                      Cont accepted validation boundaryRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier inputTraceRead traceAcceptedRead acceptedValidationBoundary boundaryPkg
  have carrierPacket :
      FiniteTraceEvaluatorCarrier input trace accepted validation transport route provenance
        localRow bundle pkg :=
    carrier
  obtain ⟨inputUnary, traceUnary, acceptedUnary, validationUnary, _transportUnary,
    _routeUnary, _provenanceUnary, localRowUnary, _inputTraceRoute,
    _routeAcceptedLocal, _acceptedValidationProvenance, _transportInputAccepted,
    provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed inputUnary traceUnary inputTraceRead
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed traceReadUnary acceptedUnary traceAcceptedRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed acceptedUnary validationUnary acceptedValidationBoundary
  have routeSameTraceRead : hsame route traceRead :=
    _inputTraceRoute.trans inputTraceRead.symm
  have localRowSameAcceptedRead : hsame localRow acceptedRead := by
    cases routeSameTraceRead
    exact _routeAcceptedLocal.trans traceAcceptedRead.symm
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            FiniteTraceEvaluatorCarrier input trace accepted validation transport route
              provenance localRow bundle pkg ∧ hsame row localRow)
          (fun row : BHist => hsame row acceptedRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
              hsame row localRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localRow ⟨carrierPacket, hsame_refl localRow⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inl (hsame_trans source.right localRowSameAcceptedRead)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, boundaryPkg, source.right⟩
    }
  exact
    ⟨cert, traceReadUnary, acceptedReadUnary, boundaryReadUnary, inputTraceRead,
      traceAcceptedRead, acceptedValidationBoundary, provenancePkg, boundaryPkg⟩

end BEDC.Derived.FiniteTraceEvaluatorUp
