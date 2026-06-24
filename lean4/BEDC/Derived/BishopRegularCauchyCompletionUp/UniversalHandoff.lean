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

theorem BishopRegularCauchyCompletionUniversalHandoff [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance localName
      toleranceRead windowRead regularRead universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus commonTail
        transport replay provenance localName bundle pkg ->
      Cont tailModulus commonTail toleranceRead ->
        Cont toleranceRead observations windowRead ->
          Cont windowRead regularity regularRead ->
            Cont regularRead endpoint universalRead ->
              PkgSig bundle universalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailModulus ∨ hsame row commonTail ∨
                        hsame row observations ∨ hsame row regularity ∨
                          hsame row endpoint ∨ hsame row universalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont tailModulus commonTail toleranceRead ∧
                        Cont toleranceRead observations windowRead ∧
                          Cont windowRead regularity regularRead ∧
                            Cont regularRead endpoint universalRead ∧
                              PkgSig bundle universalRead pkg)
                    hsame ∧
                  UnaryHistory universalRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier tailRoute windowRoute regularRoute universalRoute universalPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary observationsUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary regularityUnary regularRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed regularUnary endpointUnary universalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailModulus ∨ hsame row commonTail ∨ hsame row observations ∨
              hsame row regularity ∨ hsame row endpoint ∨ hsame row universalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailModulus commonTail toleranceRead ∧
              Cont toleranceRead observations windowRead ∧ Cont windowRead regularity regularRead ∧
                Cont regularRead endpoint universalRead ∧ PkgSig bundle universalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro universalRead ⟨hsame_refl universalRead, universalUnary⟩
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
      exact ⟨source.right, tailRoute, windowRoute, regularRoute, universalRoute, universalPkg⟩
  }
  exact ⟨cert, universalUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
