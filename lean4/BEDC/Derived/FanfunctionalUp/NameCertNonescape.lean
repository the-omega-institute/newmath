import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalNameCertNonescape [AskSetup] [PackageSetup]
    {B Q F D U T K W H R P N prefixRead barRead toleranceRead compactRead
      localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface B F U Q D W K H R P N bundle pkg ->
      Cont B Q prefixRead ->
        Cont prefixRead F barRead ->
          Cont barRead U toleranceRead ->
            Cont toleranceRead K compactRead ->
              Cont H R localRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row Q ∨ hsame row F ∨ hsame row D ∨
                            hsame row U ∨ hsame row T ∨ hsame row K ∨ hsame row W ∨
                              hsame row H ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                                hsame row localRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont B Q prefixRead ∧
                            Cont prefixRead F barRead ∧ Cont barRead U toleranceRead ∧
                              Cont toleranceRead K compactRead ∧ Cont H R localRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory prefixRead ∧ UnaryHistory barRead ∧
                        UnaryHistory toleranceRead ∧ UnaryHistory compactRead ∧
                          UnaryHistory localRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute barRoute toleranceRoute compactRoute localRoute provenancePkg
    namePkg
  obtain ⟨bUnary, fUnary, uUnary, qUnary, _dUnary, _wUnary, kUnary, hUnary, rUnary,
    _pUnary, _nUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed bUnary qUnary prefixRoute
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary fUnary barRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed barUnary uUnary toleranceRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed toleranceUnary kUnary compactRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary rUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row Q ∨ hsame row F ∨ hsame row D ∨ hsame row U ∨
              hsame row T ∨ hsame row K ∨ hsame row W ∨ hsame row H ∨ hsame row R ∨
                hsame row P ∨ hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B Q prefixRead ∧ Cont prefixRead F barRead ∧
              Cont barRead U toleranceRead ∧ Cont toleranceRead K compactRead ∧
                Cont H R localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, barRoute, toleranceRoute, compactRoute, localRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, prefixUnary, barUnary, toleranceUnary, compactUnary, localUnary⟩

end BEDC.Derived.FanfunctionalUp
