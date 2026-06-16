import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyRingCarrier [AskSetup] [PackageSetup]
    (A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧ UnaryHistory WB ∧
    UnaryHistory DA ∧ UnaryHistory DB ∧ UnaryHistory S ∧ UnaryHistory G ∧
      UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory RS ∧ UnaryHistory RG ∧
        UnaryHistory RM ∧ UnaryHistory RL ∧ UnaryHistory ES ∧ UnaryHistory EG ∧
          UnaryHistory EM ∧ UnaryHistory EL ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory P ∧ UnaryHistory N ∧ Cont A WA DA ∧ Cont B WB DB ∧
              Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyRingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      PkgSig bundle P pkg →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL
                  H C P N bundle pkg ∧ hsame row N)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
                  hsame row DA ∨ hsame row DB ∨ hsame row S ∨ hsame row G ∨
                    hsame row M ∨ hsame row L ∨ hsame row RS ∨ hsame row RG ∨
                      hsame row RM ∨ hsame row RL ∨ hsame row ES ∨ hsame row EG ∨
                        hsame row EM ∨ hsame row EL ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory M ∧ UnaryHistory L ∧
              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier provenancePkg namePkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, sUnary, gUnary, mUnary,
    lUnary, rsUnary, rgUnary, rmUnary, rlUnary, esUnary, egUnary, emUnary, elUnary,
    hUnary, cUnary, pUnary, nUnary, sourceWindowA, sourceWindowB, transportReplay,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have carrierForSource :
      RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg :=
    ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, sUnary, gUnary, mUnary,
      lUnary, rsUnary, rgUnary, rmUnary, rlUnary, esUnary, egUnary, emUnary, elUnary,
      hUnary, cUnary, pUnary, nUnary, sourceWindowA, sourceWindowB, transportReplay,
      provenancePkg, namePkg⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨carrierForSource, hsame_refl N⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
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
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        exact source.right
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport nUnary (hsame_symm source.right), provenancePkg, namePkg⟩
    }
  · exact ⟨sUnary, gUnary, mUnary, lUnary, namePkg⟩

theorem RegularCauchyRingOperationClosure [AskSetup] [PackageSetup]
    {A B WA WB DA DB ES EG EM EL H C P N S G M L RS RG RM RL : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont A B S →
        Cont A WA G →
          Cont A B M →
            Cont A WB L →
              Cont S ES RS →
                Cont G EG RG →
                  Cont M EM RM →
                    Cont L EL RL →
                      UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory M ∧
                        UnaryHistory L ∧ UnaryHistory RS ∧ UnaryHistory RG ∧
                          UnaryHistory RM ∧ UnaryHistory RL ∧ Cont S ES RS ∧
                            Cont G EG RG ∧ Cont M EM RM ∧ Cont L EL RL := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sumRoute negRoute productRoute scaleRoute sumSeal negSeal productSeal scaleSeal
  obtain ⟨unaryA, unaryB, unaryWA, unaryWB, _unaryDA, _unaryDB, _carrierUnaryS,
    _carrierUnaryG, _carrierUnaryM, _carrierUnaryL, _carrierUnaryRS, _carrierUnaryRG,
    _carrierUnaryRM, _carrierUnaryRL, unaryES, unaryEG, unaryEM, unaryEL, _unaryH,
    _unaryC, _unaryP, _unaryN, _sourceWindowA, _sourceWindowB, _transportReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have unaryS : UnaryHistory S := unary_cont_closed unaryA unaryB sumRoute
  have unaryG : UnaryHistory G := unary_cont_closed unaryA unaryWA negRoute
  have unaryM : UnaryHistory M := unary_cont_closed unaryA unaryB productRoute
  have unaryL : UnaryHistory L := unary_cont_closed unaryA unaryWB scaleRoute
  have unaryRS : UnaryHistory RS := unary_cont_closed unaryS unaryES sumSeal
  have unaryRG : UnaryHistory RG := unary_cont_closed unaryG unaryEG negSeal
  have unaryRM : UnaryHistory RM := unary_cont_closed unaryM unaryEM productSeal
  have unaryRL : UnaryHistory RL := unary_cont_closed unaryL unaryEL scaleSeal
  exact
    ⟨unaryS, unaryG, unaryM, unaryL, unaryRS, unaryRG, unaryRM, unaryRL, sumSeal,
      negSeal, productSeal, scaleSeal⟩

theorem RegularCauchyRingCarrier_componentwise_distributivity [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
      sumThenProduct leftProduct rightProduct distributedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S M sumThenProduct →
        Cont A M leftProduct →
          Cont B M rightProduct →
            Cont leftProduct rightProduct distributedRead →
              PkgSig bundle distributedRead pkg →
                UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory sumThenProduct ∧
                  UnaryHistory leftProduct ∧ UnaryHistory rightProduct ∧
                    UnaryHistory distributedRead ∧ Cont S M sumThenProduct ∧
                      Cont A M leftProduct ∧ Cont B M rightProduct ∧
                        Cont leftProduct rightProduct distributedRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle distributedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier sumProductRoute leftProductRoute rightProductRoute distributeRoute
    distributedPkg
  obtain ⟨unaryA, unaryB, _unaryWA, _unaryWB, _unaryDA, _unaryDB, unaryS, _unaryG,
    unaryM, _unaryL, _unaryRS, _unaryRG, _unaryRM, _unaryRL, _unaryES, _unaryEG,
    _unaryEM, _unaryEL, _unaryH, _unaryC, _unaryP, _unaryN, _sourceWindowA,
    _sourceWindowB, _transportReplay, provenancePkg, _namePkg⟩ := carrier
  have sumThenProductUnary : UnaryHistory sumThenProduct :=
    unary_cont_closed unaryS unaryM sumProductRoute
  have leftProductUnary : UnaryHistory leftProduct :=
    unary_cont_closed unaryA unaryM leftProductRoute
  have rightProductUnary : UnaryHistory rightProduct :=
    unary_cont_closed unaryB unaryM rightProductRoute
  have distributedUnary : UnaryHistory distributedRead :=
    unary_cont_closed leftProductUnary rightProductUnary distributeRoute
  exact
    ⟨unaryS, unaryM, sumThenProductUnary, leftProductUnary, rightProductUnary,
      distributedUnary, sumProductRoute, leftProductRoute, rightProductRoute, distributeRoute,
      provenancePkg, distributedPkg⟩

theorem RegularCauchyRingCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S ES RS →
        Cont G EG RG →
          Cont M EM RM →
            Cont L EL RL →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row RS ∨ hsame row RG ∨ hsame row RM ∨ hsame row RL)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row G ∨ hsame row M ∨ hsame row L ∨
                          hsame row RS ∨ hsame row RG ∨ hsame row RM ∨ hsame row RL)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S ES RS ∧ Cont G EG RG ∧
                          Cont M EM RM ∧ Cont L EL RL)
                      hsame ∧ UnaryHistory RS ∧ UnaryHistory RG ∧ UnaryHistory RM ∧
                    UnaryHistory RL := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory ProbeBundle Pkg
  intro carrier sumSeal negSeal productSeal scaleSeal _provenancePkg _namePkg
  obtain ⟨_unaryA, _unaryB, _unaryWA, _unaryWB, _unaryDA, _unaryDB, sUnary, gUnary,
    mUnary, lUnary, _carrierUnaryRS, _carrierUnaryRG, _carrierUnaryRM, _carrierUnaryRL,
    esUnary, egUnary, emUnary, elUnary, _unaryH, _unaryC, _unaryP, _unaryN,
    _sourceWindowA, _sourceWindowB, _transportReplay, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have rsUnary : UnaryHistory RS := unary_cont_closed sUnary esUnary sumSeal
  have rgUnary : UnaryHistory RG := unary_cont_closed gUnary egUnary negSeal
  have rmUnary : UnaryHistory RM := unary_cont_closed mUnary emUnary productSeal
  have rlUnary : UnaryHistory RL := unary_cont_closed lUnary elUnary scaleSeal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro RS (Or.inl (hsame_refl RS))
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
          intro row other sameRows source
          cases source with
          | inl sameRS =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRS)
          | inr rest =>
              cases rest with
              | inl sameRG =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRG))
              | inr rest =>
                  cases rest with
                  | inl sameRM =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRM)))
                  | inr sameRL =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRL)))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl sameRS =>
            right
            right
            right
            right
            exact Or.inl sameRS
        | inr rest =>
            cases rest with
            | inl sameRG =>
                right
                right
                right
                right
                exact Or.inr (Or.inl sameRG)
            | inr rest =>
                cases rest with
                | inl sameRM =>
                    right
                    right
                    right
                    right
                    exact Or.inr (Or.inr (Or.inl sameRM))
                | inr sameRL =>
                    right
                    right
                    right
                    right
                    exact Or.inr (Or.inr (Or.inr sameRL))
      ledger_sound := by
        intro _row source
        cases source with
        | inl sameRS =>
            exact ⟨unary_transport rsUnary (hsame_symm sameRS), sumSeal, negSeal,
              productSeal, scaleSeal⟩
        | inr rest =>
            cases rest with
            | inl sameRG =>
                exact ⟨unary_transport rgUnary (hsame_symm sameRG), sumSeal, negSeal,
                  productSeal, scaleSeal⟩
            | inr rest =>
                cases rest with
                | inl sameRM =>
                    exact ⟨unary_transport rmUnary (hsame_symm sameRM), sumSeal, negSeal,
                      productSeal, scaleSeal⟩
                | inr sameRL =>
                    exact ⟨unary_transport rlUnary (hsame_symm sameRL), sumSeal, negSeal,
                      productSeal, scaleSeal⟩
    }
  · exact ⟨rsUnary, rgUnary, rmUnary, rlUnary⟩

end BEDC.Derived.RegularCauchyRingUp
