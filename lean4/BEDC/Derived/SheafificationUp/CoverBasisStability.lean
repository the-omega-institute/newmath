import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCoverBasisStability [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverBasis siteCover sourceRead localityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverBasis →
        Cont coverBasis J siteCover →
          Cont siteCover P sourceRead →
            Cont sourceRead L localityRead →
              PkgSig bundle Q pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row localityRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                          hsame row L ∨ hsame row coverBasis ∨ hsame row siteCover ∨
                            hsame row sourceRead ∨ hsame row localityRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C T coverBasis ∧
                          Cont coverBasis J siteCover ∧ Cont siteCover P sourceRead ∧
                            Cont sourceRead L localityRead ∧ PkgSig bundle Q pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory coverBasis ∧ UnaryHistory siteCover ∧
                      UnaryHistory sourceRead ∧ UnaryHistory localityRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier coverRoute siteRoute sourceRoute localityRoute provenancePkg namePkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, lUnary, _gUnary, _sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have coverUnary : UnaryHistory coverBasis :=
    unary_cont_closed cUnary tUnary coverRoute
  have siteUnary : UnaryHistory siteCover :=
    unary_cont_closed coverUnary jUnary siteRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed siteUnary pUnary sourceRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed sourceUnary lUnary localityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row coverBasis ∨ hsame row siteCover ∨
                hsame row sourceRead ∨ hsame row localityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverBasis ∧ Cont coverBasis J siteCover ∧
              Cont siteCover P sourceRead ∧ Cont sourceRead L localityRead ∧
                PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localityRead
        ⟨hsame_refl localityRead, localityUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, siteRoute, sourceRoute, localityRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, coverUnary, siteUnary, sourceUnary, localityUnary⟩

end BEDC.Derived.SheafificationUp
