import BEDC.Derived.RegularCauchyCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCriterionCarrier [AskSetup] [PackageSetup]
    (S R M D Q V A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
    UnaryHistory Q ∧ UnaryHistory V ∧ UnaryHistory A ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S R M ∧
        Cont M D Q ∧ PkgSig bundle N pkg

theorem RegularCauchyCriterion_namecert_obligations [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N criterionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg →
      Cont Q V criterionRead →
        PkgSig bundle criterionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row criterionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
                  hsame row Q ∨ hsame row V ∨ hsame row criterionRead)
              (fun row : BHist => hsame row criterionRead ∧ PkgSig bundle criterionRead pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
              UnaryHistory Q ∧ UnaryHistory V ∧ UnaryHistory criterionRead ∧
                Cont S R M ∧ Cont M D Q ∧ Cont Q V criterionRead ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle criterionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier criterionRoute criterionPkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, _aUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, streamReadbackModulus, modulusToleranceCriterion, namePkg⟩ :=
    carrier
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed qUnary vUnary criterionRoute
  have sourceAtCriterion :
      hsame criterionRead criterionRead ∧ UnaryHistory criterionRead :=
    ⟨hsame_refl criterionRead, criterionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row criterionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
              hsame row Q ∨ hsame row V ∨ hsame row criterionRead)
          (fun row : BHist => hsame row criterionRead ∧ PkgSig bundle criterionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro criterionRead sourceAtCriterion
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
      exact ⟨source.left, criterionPkg⟩
  }
  exact
    ⟨cert, sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, criterionUnary,
      streamReadbackModulus, modulusToleranceCriterion, criterionRoute, namePkg,
      criterionPkg⟩

theorem RegularCauchyCriterion_tail_transport [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N tailRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg ->
      Cont Q V tailRead ->
        Cont tailRead A realRead ->
          PkgSig bundle realRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
                    hsame row Q ∨ hsame row V ∨ hsame row A ∨
                      hsame row tailRead ∨ hsame row realRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Q V tailRead ∧ Cont tailRead A realRead ∧
                    PkgSig bundle realRead pkg)
                hsame ∧
              UnaryHistory tailRead ∧ UnaryHistory realRead ∧ Cont Q V tailRead ∧
                Cont tailRead A realRead ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier tailRoute realRoute realPkg
  obtain ⟨_sUnary, _rUnary, _mUnary, _dUnary, qUnary, vUnary, aUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _streamReadbackModulus, _modulusToleranceCriterion,
    namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed qUnary vUnary tailRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary aUnary realRoute
  have sourceAtReal : hsame realRead realRead ∧ UnaryHistory realRead :=
    ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
              hsame row Q ∨ hsame row V ∨ hsame row A ∨ hsame row tailRead ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q V tailRead ∧ Cont tailRead A realRead ∧
              PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceAtReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, tailUnary, realUnary, tailRoute, realRoute, namePkg, realPkg⟩

theorem RegularCauchyCriterion_window_obligations [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N windowRead toleranceRead criterionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg →
      Cont S R windowRead →
        Cont M D toleranceRead →
          Cont windowRead toleranceRead criterionRead →
            PkgSig bundle criterionRead pkg →
              UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
                UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                  UnaryHistory criterionRead ∧ Cont S R windowRead ∧
                    Cont M D toleranceRead ∧ Cont windowRead toleranceRead criterionRead ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle criterionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowRoute toleranceRoute criterionRoute criterionPkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, _qUnary, _vUnary, _aUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _streamReadbackModulus, _modulusToleranceCriterion,
    namePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mUnary dUnary toleranceRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed windowUnary toleranceUnary criterionRoute
  exact
    ⟨sUnary, rUnary, mUnary, dUnary, windowUnary, toleranceUnary, criterionUnary,
      windowRoute, toleranceRoute, criterionRoute, namePkg, criterionPkg⟩

theorem RegularCauchyCriterion_modulus_route [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N dyadicRead criterionRead convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg ->
      Cont M D dyadicRead ->
        Cont dyadicRead Q criterionRead ->
          Cont criterionRead V convergenceRead ->
            PkgSig bundle convergenceRead pkg ->
              UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
                UnaryHistory dyadicRead ∧ UnaryHistory criterionRead ∧
                  UnaryHistory convergenceRead ∧ Cont S R M ∧
                    Cont M D dyadicRead ∧ Cont dyadicRead Q criterionRead ∧
                      Cont criterionRead V convergenceRead ∧ PkgSig bundle N pkg ∧
                        PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier dyadicRoute criterionRoute convergenceRoute convergencePkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, _aUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, streamReadbackModulus, _modulusToleranceCriterion, namePkg⟩ :=
    carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed mUnary dUnary dyadicRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed dyadicUnary qUnary criterionRoute
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary vUnary convergenceRoute
  exact
    ⟨sUnary, rUnary, mUnary, dUnary, dyadicUnary, criterionUnary, convergenceUnary,
      streamReadbackModulus, dyadicRoute, criterionRoute, convergenceRoute, namePkg,
      convergencePkg⟩
theorem RegularCauchyCriterionRegSeqRatRoute [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N dyadicRead regSeqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg →
      Cont D S dyadicRead →
        Cont dyadicRead R regSeqRead →
          Cont regSeqRead A realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                      hsame row dyadicRead ∨ hsame row regSeqRead ∨
                        hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D S dyadicRead ∧
                      Cont dyadicRead R regSeqRead ∧ Cont regSeqRead A realRead ∧
                        PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory dyadicRead ∧ UnaryHistory regSeqRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier dyadicRoute regSeqRoute realRoute realPkg
  obtain ⟨sUnary, rUnary, _mUnary, dUnary, _qUnary, _vUnary, aUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _streamReadbackModulus, _modulusToleranceCriterion,
    _namePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed dUnary sUnary dyadicRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed dyadicUnary rUnary regSeqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqUnary aUnary realRoute
  have sourceAtReal : hsame realRead realRead ∧ UnaryHistory realRead :=
    ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
              hsame row dyadicRead ∨ hsame row regSeqRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S dyadicRead ∧ Cont dyadicRead R regSeqRead ∧
              Cont regSeqRead A realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceAtReal
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
      exact ⟨source.right, dyadicRoute, regSeqRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, dyadicUnary, regSeqUnary, realUnary⟩

end BEDC.Derived.RegularCauchyCriterionUp
