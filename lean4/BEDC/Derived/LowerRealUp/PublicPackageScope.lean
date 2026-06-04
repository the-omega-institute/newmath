import BEDC.Derived.LowerRealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LowerRealPublicPackage [AskSetup] [PackageSetup]
    (L0 W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ∧
    UnaryHistory L0 ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem LowerRealPublicPackage_scope
    {L0 W R E H C P N locatedRead sealRead publicRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] ->
      UnaryHistory L0 ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont L0 W locatedRead ->
                Cont locatedRead R sealRead ->
                  Cont sealRead E publicRead ->
                    UnaryHistory locatedRead ∧
                      UnaryHistory sealRead ∧
                        UnaryHistory publicRead ∧
                          hsame (lowerRealDecodeBHist (lowerRealEncodeBHist N)) N := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows l0Unary windowUnary regularUnary sealUnary locatedRoute sealRoute publicRoute
  cases fieldRows
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed l0Unary windowUnary locatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedUnary regularUnary sealRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary sealUnary publicRoute
  have nameDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist N)) N := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist N) = N
    exact LowerRealTasteGate_single_carrier_alignment.1 N
  exact ⟨locatedUnary, sealReadUnary, publicReadUnary, nameDecode⟩

theorem LowerRealLocatedCutSealBoundary [AskSetup] [PackageSetup]
    {L0 W R E H C P N lowerRead rationalRead realRead namedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LowerRealPublicPackage L0 W R E H C P N bundle pkg →
      Cont L0 W lowerRead →
        Cont lowerRead R rationalRead →
          Cont rationalRead E realRead →
            Cont realRead N namedRead →
              Cont namedRead E sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L0 ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                          hsame row N ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L0 W lowerRead ∧
                          Cont lowerRead R rationalRead ∧ Cont rationalRead E realRead ∧
                            Cont realRead N namedRead ∧ Cont namedRead E sealRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro package lowerRoute rationalRoute realRoute namedRoute sealRoute sealPkg
  obtain ⟨fieldRows, l0Unary, wUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, pPkg, _nPkg⟩ := package
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed l0Unary wUnary lowerRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerUnary rUnary rationalRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rationalUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed namedUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L0 W lowerRead ∧ Cont lowerRead R rationalRead ∧
              Cont rationalRead E realRead ∧ Cont realRead N namedRead ∧
                Cont namedRead E sealRead ∧ PkgSig bundle P pkg ∧
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, rationalRoute, realRoute, namedRoute, sealRoute,
          pPkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LowerRealUp
