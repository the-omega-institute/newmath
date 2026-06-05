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

theorem BishopRegularCauchyCompletionAbstractBridgeRoute [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName completionRead supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg ->
      Cont commonTail transport completionRead ->
        Cont completionRead replay supportRead ->
          PkgSig bundle provenance pkg ->
            PkgSig bundle localName pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
                      hsame row tailModulus ∨ hsame row commonTail ∨ hsame row supportRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont commonTail transport completionRead ∧
                      Cont completionRead replay supportRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory supportRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier commonTransport completionReplay provenancePkg localNamePkg
  obtain ⟨_endpointUnary, _observationsUnary, _regularityUnary, _tailModulusUnary,
    commonTailUnary, transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed commonTailUnary transportUnary commonTransport
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed completionUnary replayUnary completionReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
              hsame row tailModulus ∨ hsame row commonTail ∨ hsame row supportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonTail transport completionRead ∧
              Cont completionRead replay supportRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supportRead
        ⟨hsame_refl supportRead, supportUnary⟩
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
      exact ⟨source.right, commonTransport, completionReplay, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completionUnary, supportUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
