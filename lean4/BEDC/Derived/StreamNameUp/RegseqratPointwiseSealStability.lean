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

theorem StreamnameRegseqratPointwiseSealStability [AskSetup] [PackageSetup]
    {window overlap classifier bundleLedger membership observation dyadic sealLeft sealRight
      publicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window ->
      UnaryHistory overlap ->
        UnaryHistory classifier ->
          UnaryHistory bundleLedger ->
            UnaryHistory membership ->
              UnaryHistory observation ->
                UnaryHistory dyadic ->
                  Cont window overlap classifier ->
                    Cont classifier dyadic sealLeft ->
                      Cont bundleLedger membership sealRight ->
                        Cont sealLeft sealRight publicSeal ->
                          PkgSig bundle publicSeal pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row publicSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row window ∨ hsame row overlap ∨
                                    hsame row classifier ∨ hsame row dyadic ∨
                                      hsame row publicSeal)
                                (fun _row : BHist =>
                                  Cont window overlap classifier ∧
                                    Cont classifier dyadic sealLeft ∧
                                      Cont bundleLedger membership sealRight ∧
                                        Cont sealLeft sealRight publicSeal ∧
                                          PkgSig bundle publicSeal pkg)
                                hsame ∧ UnaryHistory sealLeft ∧ UnaryHistory sealRight ∧
                              UnaryHistory publicSeal := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert
  intro windowUnary overlapUnary classifierUnary bundleLedgerUnary membershipUnary
    _observationUnary dyadicUnary windowOverlap classifierDyadic bundleMembership
    publicSealRoute pkgRow
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed classifierUnary dyadicUnary classifierDyadic
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed bundleLedgerUnary membershipUnary bundleMembership
  have publicSealUnary : UnaryHistory publicSeal :=
    unary_cont_closed sealLeftUnary sealRightUnary publicSealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row window ∨ hsame row overlap ∨ hsame row classifier ∨ hsame row dyadic ∨
            hsame row publicSeal)
        (fun _row : BHist =>
          Cont window overlap classifier ∧ Cont classifier dyadic sealLeft ∧
            Cont bundleLedger membership sealRight ∧ Cont sealLeft sealRight publicSeal ∧
              PkgSig bundle publicSeal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicSeal
        ⟨hsame_refl publicSeal, publicSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row _source
      exact ⟨windowOverlap, classifierDyadic, bundleMembership, publicSealRoute, pkgRow⟩
  }
  exact ⟨cert, sealLeftUnary, sealRightUnary, publicSealUnary⟩

end BEDC.Derived.StreamNameUp
