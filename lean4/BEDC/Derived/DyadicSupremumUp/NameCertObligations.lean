import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicSupremumNameCertObligations [AskSetup] [PackageSetup]
    {bounded lowerApprox window tolerance readback realSeal _transport _replay provenance localName
      upperRead lowerRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory bounded →
      UnaryHistory lowerApprox →
        UnaryHistory window →
          UnaryHistory tolerance →
            UnaryHistory readback →
              UnaryHistory realSeal →
                Cont bounded tolerance upperRead →
                  Cont lowerApprox window lowerRead →
                    Cont upperRead lowerRead handoffRead →
                      Cont handoffRead readback realSeal →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row bounded ∨ hsame row lowerApprox ∨
                                    hsame row window ∨ hsame row tolerance ∨
                                      hsame row upperRead ∨ hsame row lowerRead ∨
                                        hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont upperRead lowerRead handoffRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                                UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro boundedUnary lowerApproxUnary windowUnary toleranceUnary readbackUnary _realSealUnary
    upperRoute lowerRoute handoffRoute sealRoute provenancePkg localNamePkg
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed boundedUnary toleranceUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerApproxUnary windowUnary lowerRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed upperUnary lowerUnary handoffRoute
  have _sealUnaryFromRoute : UnaryHistory realSeal :=
    unary_cont_closed handoffUnary readbackUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bounded ∨ hsame row lowerApprox ∨ hsame row window ∨
              hsame row tolerance ∨ hsame row upperRead ∨ hsame row lowerRead ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont upperRead lowerRead handoffRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, handoffRoute, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, upperUnary, lowerUnary, handoffUnary⟩

end BEDC.Derived.DyadicSupremumUp
