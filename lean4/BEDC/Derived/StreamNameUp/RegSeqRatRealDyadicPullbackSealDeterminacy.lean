import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameRegseqratRealDyadicPullbackSealDeterminacy [AskSetup] [PackageSetup]
    {window regseqRead dyadicLedger realSeal route name provenance sealConsumer : BHist}
    {probe : ProbeName} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InBundle probe bundle ->
      UnaryHistory window ->
        UnaryHistory regseqRead ->
          UnaryHistory dyadicLedger ->
            UnaryHistory realSeal ->
              UnaryHistory name ->
                Cont window regseqRead dyadicLedger ->
                  Cont dyadicLedger realSeal route ->
                    Cont route name sealConsumer ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle sealConsumer pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row sealConsumer ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row sealConsumer ∧ InBundle probe bundle ∧
                                  Cont window regseqRead dyadicLedger)
                              (fun row : BHist =>
                                hsame row sealConsumer ∧ Cont route name sealConsumer ∧
                                  PkgSig bundle sealConsumer pkg)
                              hsame ∧
                            UnaryHistory route ∧ UnaryHistory sealConsumer ∧
                              InBundle probe bundle ∧ Cont window regseqRead dyadicLedger ∧
                                Cont dyadicLedger realSeal route ∧
                                  Cont route name sealConsumer ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle sealConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert hsame
  intro probeMember windowUnary regseqUnary _dyadicUnary realSealUnary nameUnary
    windowRegseqDyadic dyadicRealRoute routeNameSeal provenancePkg sealPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed _dyadicUnary realSealUnary dyadicRealRoute
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed routeUnary nameUnary routeNameSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealConsumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealConsumer ∧ InBundle probe bundle ∧
              Cont window regseqRead dyadicLedger)
          (fun row : BHist =>
            hsame row sealConsumer ∧ Cont route name sealConsumer ∧
              PkgSig bundle sealConsumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealConsumer ⟨hsame_refl sealConsumer, sealUnary⟩
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
      exact ⟨source.left, probeMember, windowRegseqDyadic⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeNameSeal, sealPkg⟩
  }
  exact
    ⟨cert, routeUnary, sealUnary, probeMember, windowRegseqDyadic, dyadicRealRoute,
      routeNameSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.StreamNameUp
