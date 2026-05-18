import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryPublicBridge [AskSetup] [PackageSetup]
    {e a t v h c p n publicRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont h c publicRead ->
          Cont v h refusalRead ->
            PkgSig bundle publicRead pkg ->
              PkgSig bundle refusalRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                      hsame row publicRead)
                  (fun row : BHist =>
                    Cont e t h ∧ Cont h c row ∧ PkgSig bundle publicRead pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                  UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory publicRead ∧
                      UnaryHistory refusalRead ∧ Cont e a v ∧ Cont e t h ∧
                        Cont h c publicRead ∧ Cont v h refusalRead ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧
                            PkgSig bundle refusalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier eav publicRoute refusalRoute publicPkg refusalPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEav, eth, _hcn, pPkg, _nPkg, hn⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary cUnary publicRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary refusalRoute
  have publicCert :
      SemanticNameCert
        (fun row : BHist =>
          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
            hsame row publicRead)
        (fun row : BHist => Cont e t h ∧ Cont h c row ∧ PkgSig bundle publicRead pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        (And.intro carrierWitness (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact And.intro eth
        (And.intro (cont_result_hsame_transport publicRoute (hsame_symm source.right))
          publicPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport publicUnary (hsame_symm source.right)) publicPkg
  }
  exact
    ⟨publicCert, eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, publicUnary,
      refusalUnary, eav, eth, publicRoute, refusalRoute, pPkg, publicPkg, refusalPkg, hn⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
