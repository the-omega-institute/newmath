import BEDC.Derived.BishopRegularCauchyCompletionUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionPublicRealSeal [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont tailModulus commonTail replay →
        Cont replay endpoint realSealRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
                      hsame row tailModulus ∨ hsame row commonTail ∨ hsame row realSealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont tailModulus commonTail replay ∧
                      Cont replay endpoint realSealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier tailCommon replayEndpoint provenancePkg localNamePkg
  obtain ⟨endpointUnary, _observationsUnary, _regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed replayUnary endpointUnary replayEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
              hsame row tailModulus ∨ hsame row commonTail ∨ hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailModulus commonTail replay ∧
              Cont replay endpoint realSealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSealRead ⟨hsame_refl realSealRead, realSealUnary⟩
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
      exact ⟨source.right, tailCommon, replayEndpoint, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, realSealUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
