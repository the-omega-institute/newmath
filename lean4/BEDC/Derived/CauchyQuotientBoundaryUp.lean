import BEDC.Derived.CauchyQuotientBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyQuotientBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyQuotientBoundaryCarrier [AskSetup] [PackageSetup]
    (S Q F D W R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory ProbeBundle Pkg PkgSig
  UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory F ∧ UnaryHistory D ∧
    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem CauchyQuotientBoundaryCarrier_refusal_factorization [AskSetup] [PackageSetup]
    {S Q F D W R E H C P N sourceRead refusalRead dyadicRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyQuotientBoundaryCarrier S Q F D W R E H C P N bundle pkg →
      Cont S W sourceRead →
        Cont sourceRead F refusalRead →
          Cont refusalRead D dyadicRead →
            Cont dyadicRead R readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory sourceRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory sealRead ∧ Cont S W sourceRead ∧
                        Cont sourceRead F refusalRead ∧ Cont refusalRead D dyadicRead ∧
                          Cont dyadicRead R readbackRead ∧
                            Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier sourceRoute refusalRoute dyadicRoute readbackRoute sealRoute sealPkg
  obtain ⟨sUnary, _qUnary, fUnary, dUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary wUnary sourceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sourceUnary fUnary refusalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed refusalUnary dUnary dyadicRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed dyadicUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact
    ⟨sourceUnary, refusalUnary, dyadicUnary, readbackUnary, sealUnary, sourceRoute,
      refusalRoute, dyadicRoute, readbackRoute, sealRoute, provenancePkg, sealPkg⟩

theorem CauchyQuotientBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S Q F D W R E H C P N quotientRead refusalRead dyadicRead windowRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyQuotientBoundaryCarrier S Q F D W R E H C P N bundle pkg →
      Cont S Q quotientRead →
        Cont quotientRead F refusalRead →
          Cont refusalRead D dyadicRead →
            Cont dyadicRead W windowRead →
              Cont windowRead R readbackRead →
                Cont readbackRead E sealRead →
                  UnaryHistory quotientRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier quotientRoute refusalRoute dyadicRoute windowRoute readbackRoute sealRoute
  obtain ⟨sUnary, qUnary, fUnary, dUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have quotientUnary : UnaryHistory quotientRead :=
    unary_cont_closed sUnary qUnary quotientRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed quotientUnary fUnary refusalRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed refusalUnary dUnary dyadicRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact ⟨quotientUnary, refusalUnary, dyadicUnary, windowUnary, readbackUnary, sealUnary,
    provenancePkg⟩

theorem CauchyQuotientBoundaryRealSealNonescape [AskSetup] [PackageSetup]
    {S Q F D W R E H C P N readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyQuotientBoundaryCarrier S Q F D W R E H C P N bundle pkg →
      Cont R E sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row S ∨ hsame row Q ∨ hsame row F ∨ hsame row D ∨ hsame row W ∨
                hsame row R ∨ hsame row E ∨ hsame row sealRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont R E sealRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle sealRead pkg)
            hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  obtain ⟨_sUnary, _qUnary, _fUnary, _dUnary, _wUnary, rUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row Q ∨ hsame row F ∨ hsame row D ∨ hsame row W ∨
            hsame row R ∨ hsame row E ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont R E sealRead ∧ PkgSig bundle P pkg ∧
            PkgSig bundle sealRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact ⟨source.right, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CauchyQuotientBoundaryUp
