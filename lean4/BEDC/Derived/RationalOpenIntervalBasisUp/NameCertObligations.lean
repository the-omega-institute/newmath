import BEDC.Derived.RationalOpenIntervalBasisUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalOpenIntervalBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalOpenIntervalBasisCarrier [AskSetup] [PackageSetup]
    (Q D M S G E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame NameCert
  UnaryHistory Q ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory S ∧
    UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ hsame H N ∧ PkgSig bundle P pkg

theorem RationalOpenIntervalBasisCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q D M S G E H C P N centerRadius membershipRead windowRead handoffRead sealRead
      localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalOpenIntervalBasisCarrier Q D M S G E H C P N bundle pkg →
      Cont Q D centerRadius →
        Cont centerRadius M membershipRead →
          Cont membershipRead S windowRead →
            Cont windowRead G handoffRead →
              Cont handoffRead E sealRead →
                Cont sealRead N localRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle localRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨
                              hsame row G ∨ hsame row E ∨ hsame row N ∨
                                hsame row localRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Q D centerRadius ∧
                              Cont centerRadius M membershipRead ∧
                                Cont membershipRead S windowRead ∧
                                  Cont windowRead G handoffRead ∧
                                    Cont handoffRead E sealRead ∧
                                      Cont sealRead N localRead ∧
                                        PkgSig bundle P pkg ∧
                                          PkgSig bundle localRead pkg)
                          hsame ∧
                        UnaryHistory centerRadius ∧ UnaryHistory membershipRead ∧
                          UnaryHistory windowRead ∧ UnaryHistory handoffRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: RationalOpenIntervalBasisCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qd centerMembership membershipWindow windowHandoff handoffSeal sealLocal
    pkgP pkgLocal
  obtain
    ⟨qUnary, dUnary, mUnary, sUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary,
      nUnary, _sameHN, _carrierPkg⟩ := carrier
  have centerUnary : UnaryHistory centerRadius :=
    unary_cont_closed qUnary dUnary qd
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed centerUnary mUnary centerMembership
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed membershipUnary sUnary membershipWindow
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary gUnary windowHandoff
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary eUnary handoffSeal
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed sealUnary nUnary sealLocal
  have sourceLocal :
      (fun row : BHist => hsame row localRead ∧ UnaryHistory row) localRead := by
    exact ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨ hsame row G ∨
              hsame row E ∨ hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q D centerRadius ∧
              Cont centerRadius M membershipRead ∧ Cont membershipRead S windowRead ∧
                Cont windowRead G handoffRead ∧ Cont handoffRead E sealRead ∧
                  Cont sealRead N localRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceLocal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qd, centerMembership, membershipWindow, windowHandoff,
          handoffSeal, sealLocal, pkgP, pkgLocal⟩
  }
  exact
    ⟨cert, centerUnary, membershipUnary, windowUnary, handoffUnary, sealUnary,
      localUnary⟩

end BEDC.Derived.RationalOpenIntervalBasisUp
