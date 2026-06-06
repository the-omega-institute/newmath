import BEDC.Derived.UpperSemicontinuousUp.FiniteWindowStability
import BEDC.Derived.UpperSemicontinuousUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UpperSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem UpperSemicontinuousLowerDualBoundary [AskSetup] [PackageSetup]
    {W R O H N lowerW lowerR lowerO lowerH lowerN upperWindow upperRead upperSeal
      lowerWindow lowerRead lowerSeal P lowerP : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory R →
        UnaryHistory O →
          UnaryHistory H →
            UnaryHistory N →
              UnaryHistory lowerW →
                UnaryHistory lowerR →
                  UnaryHistory lowerO →
                    UnaryHistory lowerH →
                      UnaryHistory lowerN →
                        Cont W R upperWindow →
                          Cont upperWindow O upperRead →
                            Cont upperRead H upperSeal →
                              Cont lowerW lowerR lowerWindow →
                                Cont lowerWindow lowerO lowerRead →
                                  Cont lowerRead lowerH lowerSeal →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle lowerP pkg →
                                        PkgSig bundle upperSeal pkg →
                                          PkgSig bundle lowerSeal pkg →
                                            Nonempty (BHistCarrier UpperSemicontinuousUp) ∧
                                              SemanticNameCert
                                                (fun row : BHist =>
                                                  (hsame row upperSeal ∨
                                                      hsame row lowerSeal) ∧
                                                    UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row W ∨ hsame row R ∨
                                                    hsame row O ∨ hsame row H ∨
                                                      hsame row lowerW ∨
                                                        hsame row lowerR ∨
                                                          hsame row lowerO ∨
                                                            hsame row lowerH ∨
                                                              hsame row upperSeal ∨
                                                                hsame row lowerSeal)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    PkgSig bundle upperSeal pkg ∧
                                                      PkgSig bundle lowerSeal pkg)
                                                hsame ∧
                                                UnaryHistory upperSeal ∧
                                                  UnaryHistory lowerSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryW unaryR unaryO unaryH _unaryN unaryLowerW unaryLowerR unaryLowerO
    unaryLowerH _unaryLowerN upperWindowCont upperReadCont upperSealCont
    lowerWindowCont lowerReadCont lowerSealCont _upperProvenance _lowerProvenance
    upperSealPkg lowerSealPkg
  have upperWindowUnary : UnaryHistory upperWindow :=
    unary_cont_closed unaryW unaryR upperWindowCont
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed upperWindowUnary unaryO upperReadCont
  have upperSealUnary : UnaryHistory upperSeal :=
    unary_cont_closed upperReadUnary unaryH upperSealCont
  have lowerWindowUnary : UnaryHistory lowerWindow :=
    unary_cont_closed unaryLowerW unaryLowerR lowerWindowCont
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerWindowUnary unaryLowerO lowerReadCont
  have lowerSealUnary : UnaryHistory lowerSeal :=
    unary_cont_closed lowerReadUnary unaryLowerH lowerSealCont
  have cert :
      SemanticNameCert
        (fun row : BHist => (hsame row upperSeal ∨ hsame row lowerSeal) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row W ∨ hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row lowerW ∨
            hsame row lowerR ∨ hsame row lowerO ∨ hsame row lowerH ∨
              hsame row upperSeal ∨ hsame row lowerSeal)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle upperSeal pkg ∧ PkgSig bundle lowerSeal pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro upperSeal
          (And.intro (Or.inl (hsame_refl upperSeal)) upperSealUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        have otherUnary : UnaryHistory _ := unary_transport source.right same
        cases source.left with
        | inl sameUpper =>
            exact And.intro
              (Or.inl (hsame_trans (hsame_symm same) sameUpper)) otherUnary
        | inr sameLower =>
            exact And.intro
              (Or.inr (hsame_trans (hsame_symm same) sameLower)) otherUnary
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameUpper =>
          right
          right
          right
          right
          right
          right
          right
          right
          left
          exact sameUpper
      | inr sameLower =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact sameLower
    ledger_sound := by
      intro _row source
      exact ⟨source.right, upperSealPkg, lowerSealPkg⟩
  }
  exact ⟨Nonempty.intro upperSemicontinuousBHistCarrier, cert, upperSealUnary, lowerSealUnary⟩

theorem UpperSemicontinuousCarrier_lower_dual_boundary [AskSetup] [PackageSetup]
    {X F S W R O H C P N upperRead lowerGraph lowerWindow lowerRead lowerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory F →
        UnaryHistory S →
          UnaryHistory W →
            UnaryHistory R →
              UnaryHistory O →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        UnaryHistory lowerGraph →
                          UnaryHistory lowerWindow →
                            PkgSig bundle P pkg →
                              Cont F W upperRead →
                                Cont lowerGraph lowerWindow lowerRead →
                                  Cont lowerRead O lowerSeal →
                                    PkgSig bundle upperRead pkg →
                                      PkgSig bundle lowerSeal pkg →
                                        UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧
                                          UnaryHistory W ∧ UnaryHistory R ∧
                                            UnaryHistory O ∧ UnaryHistory upperRead ∧
                                              UnaryHistory lowerRead ∧
                                                UnaryHistory lowerSeal ∧
                                                  Cont F W upperRead ∧
                                                    Cont lowerGraph lowerWindow lowerRead ∧
                                                      Cont lowerRead O lowerSeal ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle upperRead pkg ∧
                                                            PkgSig bundle lowerSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro xUnary fUnary sUnary wUnary rUnary oUnary _hUnary _cUnary _pUnary _nUnary
    lowerGraphUnary lowerWindowUnary provenancePkg upperRoute lowerReadRoute lowerSealRoute
    upperPkg lowerSealPkg
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed fUnary wUnary upperRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerGraphUnary lowerWindowUnary lowerReadRoute
  have lowerSealUnary : UnaryHistory lowerSeal :=
    unary_cont_closed lowerReadUnary oUnary lowerSealRoute
  exact
    ⟨xUnary, fUnary, sUnary, wUnary, rUnary, oUnary, upperReadUnary, lowerReadUnary,
      lowerSealUnary, upperRoute, lowerReadRoute, lowerSealRoute, provenancePkg, upperPkg,
      lowerSealPkg⟩

end BEDC.Derived.UpperSemicontinuousUp
