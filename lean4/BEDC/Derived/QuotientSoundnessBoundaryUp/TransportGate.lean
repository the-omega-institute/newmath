import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_transport_gate [AskSetup] [PackageSetup]
    {e a t v h c p n rootDemand refusalRead transportRead gatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a rootDemand ->
        Cont v t refusalRead ->
          Cont t h transportRead ->
            Cont transportRead n gatedRead ->
              PkgSig bundle rootDemand pkg ->
                PkgSig bundle gatedRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        Cont e a rootDemand ∧ Cont v t refusalRead ∧
                          Cont t h transportRead ∧ Cont transportRead n gatedRead ∧
                            hsame row gatedRead)
                    (fun row : BHist =>
                      Cont e a rootDemand ∧ Cont v t refusalRead ∧
                        Cont t h transportRead ∧ Cont transportRead n row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                        PkgSig bundle rootDemand pkg ∧ PkgSig bundle gatedRead pkg ∧
                          hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rootRequest vTRefusal tHTransport transportGate rootPkg gatedPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, nUnary,
    _eAV, _eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have _refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have gatedUnary : UnaryHistory gatedRead :=
    unary_cont_closed transportUnary nUnary transportGate
  exact {
    core := {
      carrier_inhabited := Exists.intro gatedRead
        (And.intro carrierWitness
          (And.intro rootRequest
            (And.intro vTRefusal
              (And.intro tHTransport (And.intro transportGate (hsame_refl gatedRead))))))
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            source.right.right.right.left, source.right.right.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.right.left, source.right.right.left, source.right.right.right.left,
          cont_result_hsame_transport transportGate
            (hsame_symm source.right.right.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport gatedUnary (hsame_symm source.right.right.right.right.right), pPkg,
          nPkg, rootPkg, gatedPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
