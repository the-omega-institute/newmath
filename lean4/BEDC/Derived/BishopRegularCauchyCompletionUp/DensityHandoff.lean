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

theorem BishopRegularCauchyCompletionCarrier_density_handoff [AskSetup] [PackageSetup]
    {endpoint stream regular dyadic tail transport replay provenance localName streamRegular
      regularDyadic dyadicTail tailSeal densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint stream regular dyadic tail transport replay
        provenance localName bundle pkg →
      Cont stream regular streamRegular →
        Cont streamRegular dyadic regularDyadic →
          Cont regularDyadic tail dyadicTail →
            Cont dyadicTail endpoint tailSeal →
              Cont tailSeal provenance densityRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle densityRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row endpoint ∨ hsame row stream ∨ hsame row regular ∨
                            hsame row dyadic ∨ hsame row tail ∨ hsame row transport ∨
                              hsame row replay ∨ hsame row provenance ∨
                                hsame row localName ∨ hsame row densityRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle densityRead pkg)
                        hsame ∧
                      UnaryHistory streamRegular ∧ UnaryHistory regularDyadic ∧
                        UnaryHistory dyadicTail ∧ UnaryHistory tailSeal ∧
                          UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg
  -- Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute dyadicRoute tailRoute sealRoute densityRoute provenancePkg densityPkg
  obtain ⟨endpointUnary, streamUnary, regularUnary, dyadicUnary, tailUnary, _transportUnary,
    _replayUnary, provenanceUnary, _localNameUnary, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrier
  have streamRegularUnary : UnaryHistory streamRegular :=
    unary_cont_closed streamUnary regularUnary streamRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed streamRegularUnary dyadicUnary dyadicRoute
  have dyadicTailUnary : UnaryHistory dyadicTail :=
    unary_cont_closed regularDyadicUnary tailUnary tailRoute
  have tailSealUnary : UnaryHistory tailSeal :=
    unary_cont_closed dyadicTailUnary endpointUnary sealRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed tailSealUnary provenanceUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row stream ∨ hsame row regular ∨
              hsame row dyadic ∨ hsame row tail ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
      exact ⟨source.right, provenancePkg, densityPkg⟩
  }
  exact
    ⟨cert, streamRegularUnary, regularDyadicUnary, dyadicTailUnary, tailSealUnary,
      densityUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
