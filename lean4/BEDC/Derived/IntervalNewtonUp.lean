import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalNewtonCarrier [AskSetup] [PackageSetup]
    (B F D N K V R H C P L : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory D ∧ UnaryHistory N ∧
    UnaryHistory K ∧ UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧ Cont V R L ∧
        PkgSig bundle L pkg

theorem IntervalNewtonKrawczykEnclosure [AskSetup] [PackageSetup]
    {B F D N K V R H C P L narrowed : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K narrowed ->
        PkgSig bundle narrowed pkg ->
          UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧ UnaryHistory V ∧
            UnaryHistory narrowed ∧ Cont N K narrowed ∧ PkgSig bundle L pkg ∧
              PkgSig bundle narrowed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier narrowedRoute narrowedPkg
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, localPkg⟩ := carrier
  have unaryNarrowed : UnaryHistory narrowed :=
    unary_cont_closed unaryN unaryK narrowedRoute
  exact
    ⟨unaryB, unaryN, unaryK, unaryV, unaryNarrowed, narrowedRoute, localPkg, narrowedPkg⟩

theorem IntervalNewtonNameCertObligations [AskSetup] [PackageSetup]
    {B F D N K V R H C P L containment validatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K containment ->
        Cont containment V validatedRead ->
          PkgSig bundle validatedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row N ∨ hsame row K ∨ hsame row V ∨
                    hsame row validatedRead)
                (fun row : BHist =>
                  hsame row validatedRead ∧ PkgSig bundle validatedRead pkg)
                hsame ∧
              UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧
                UnaryHistory containment ∧ UnaryHistory validatedRead ∧
                  Cont N K containment ∧ Cont containment V validatedRead ∧
                    PkgSig bundle L pkg ∧ PkgSig bundle validatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier containmentRoute validatedRoute validatedPkg
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, localPkg⟩ := carrier
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed unaryN unaryK containmentRoute
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed containmentUnary unaryV validatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row N ∨ hsame row K ∨ hsame row V ∨
              hsame row validatedRead)
          (fun row : BHist =>
            hsame row validatedRead ∧ PkgSig bundle validatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro validatedRead ⟨hsame_refl validatedRead, validatedUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, validatedPkg⟩
  }
  exact
    ⟨cert, unaryB, unaryN, unaryK, containmentUnary, validatedUnary, containmentRoute,
      validatedRoute, localPkg, validatedPkg⟩

theorem IntervalNewtonContainmentObligation [AskSetup] [PackageSetup]
    {B F D N K V R H C P L containment : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg →
      Cont N K containment →
        UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧ UnaryHistory containment ∧
          Cont N K containment ∧ PkgSig bundle L pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier containmentRoute
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, _unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _localRoute, localPkg⟩ := carrier
  have unaryContainment : UnaryHistory containment :=
    unary_cont_closed unaryN unaryK containmentRoute
  exact ⟨unaryB, unaryN, unaryK, unaryContainment, containmentRoute, localPkg⟩

end BEDC.Derived.IntervalNewtonUp
