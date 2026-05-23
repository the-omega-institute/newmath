import BEDC.Derived.RealityConstrainedApproximationTowerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedApproximationTowerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem RealityConstrainedApproximationTowerNonescape [AskSetup] [PackageSetup]
    {O D M S C F L H R P N modelRead signatureRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont O D modelRead →
      Cont modelRead S signatureRead →
        Cont signatureRead F ledgerRead →
          Cont ledgerRead L publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row publicRead ∧
                      FieldFaithful.fields
                          (RealityConstrainedApproximationTowerUp.mk O D M S C F L H R P N) =
                        [O, D, M, S, C, F, L, H, R, P, N])
                  (fun _row : BHist =>
                    Cont signatureRead F ledgerRead ∧ Cont ledgerRead L publicRead)
                  (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                Cont signatureRead F ledgerRead ∧ Cont ledgerRead L publicRead ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame FieldFaithful SemanticNameCert
  intro _modelRoute _signatureRoute signatureLedgerRoute ledgerPublicRoute publicPkg
  have fieldsExact :
      FieldFaithful.fields
          (RealityConstrainedApproximationTowerUp.mk O D M S C F L H R P N) =
        [O, D, M, S, C, F, L, H, R, P, N] := by
    rfl
  have sourceAtPublic :
      hsame publicRead publicRead ∧
        FieldFaithful.fields
            (RealityConstrainedApproximationTowerUp.mk O D M S C F L H R P N) =
          [O, D, M, S, C, F, L, H, R, P, N] := by
    exact ⟨hsame_refl publicRead, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧
              FieldFaithful.fields
                  (RealityConstrainedApproximationTowerUp.mk O D M S C F L H R P N) =
                [O, D, M, S, C, F, L, H, R, P, N])
          (fun _row : BHist =>
            Cont signatureRead F ledgerRead ∧ Cont ledgerRead L publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨signatureLedgerRoute, ledgerPublicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact ⟨cert, signatureLedgerRoute, ledgerPublicRoute, publicPkg⟩

end BEDC.Derived.RealityConstrainedApproximationTowerUp
