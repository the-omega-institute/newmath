import BEDC.Derived.BedcPhilosophyPackageUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BedcPhilosophyPackageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BedcPhilosophyPackageCarrier [AskSetup] [PackageSetup]
    (T R M G D S C A H K N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory D ∧
    UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory K ∧
      UnaryHistory N ∧ Cont T R K ∧ Cont M G K ∧ Cont S A K ∧ Cont C A K ∧
        PkgSig bundle K pkg ∧ PkgSig bundle N pkg

theorem BedcPhilosophyPackage_namecert_obligations [AskSetup] [PackageSetup]
    {T R M G D S C A H K N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  have sourceN :
      (fun row : BHist =>
        BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ∧ hsame row N) N := by
    exact ⟨carrier, hsame_refl N⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem BedcPhilosophyPackage_audit_map_nonescape [AskSetup] [PackageSetup]
    {T R M G D S C A H K N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      UnaryHistory S ∧ UnaryHistory A ∧ Cont S A K ∧
        PkgSig bundle K pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  exact
    ⟨carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem BedcPhilosophyPackageRegistryLedgerExactness [AskSetup] [PackageSetup]
    {T R M G D S C A H K N registryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg ->
      Cont R M registryRead ->
        PkgSig bundle registryRead pkg ->
          UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory G ∧
            UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory A ∧
              UnaryHistory registryRead ∧ Cont R M registryRead ∧
                PkgSig bundle registryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier registryRoute registryPkg
  obtain ⟨thesisUnary, registryUnary, theoremMapUnary, gapMapUnary, traditionUnary,
    cannotClaimUnary, closureUnary, auditUnary, _transportUnary, _routeUnary,
      _nameUnary, _thesisRegistryRoute, _theoremGapRoute, _cannotAuditRoute,
      _closureAuditRoute, _routePkg, _namePkg⟩ := carrier
  have registryReadUnary : UnaryHistory registryRead :=
    unary_cont_closed registryUnary theoremMapUnary registryRoute
  exact
    ⟨thesisUnary, registryUnary, theoremMapUnary, gapMapUnary, traditionUnary,
      cannotClaimUnary, closureUnary, auditUnary, registryReadUnary,
      registryRoute, registryPkg⟩

end BEDC.Derived.BedcPhilosophyPackageUp
