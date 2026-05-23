import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SemiringUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SemiringLedger [AskSetup] [PackageSetup]
    (additive multiplicative shared distributive annihilation transport route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory additive ∧ UnaryHistory multiplicative ∧ UnaryHistory shared ∧
    UnaryHistory distributive ∧ UnaryHistory annihilation ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory endpoint ∧ Cont additive multiplicative shared ∧
        Cont shared distributive transport ∧ Cont transport annihilation route ∧
          Cont route transport endpoint ∧ PkgSig bundle endpoint pkg

theorem SemiringLedger_namecert_obligation_surface [AskSetup] [PackageSetup]
    {additive multiplicative shared distributive annihilation transport route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringLedger additive multiplicative shared distributive annihilation transport route
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            SemiringLedger additive multiplicative shared distributive annihilation transport route
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame := by
  intro ledger
  let Surface : BHist -> Prop :=
    fun row : BHist =>
      SemiringLedger additive multiplicative shared distributive annihilation transport route
        endpoint bundle pkg ∧ hsame row endpoint
  have endpointSource : Surface endpoint :=
    And.intro ledger (hsame_refl endpoint)
  have core : NameCert Surface hsame := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' same
      exact hsame_symm same
    equiv_trans := by
      intro _row _row' _row'' sameRow sameRow'
      exact hsame_trans sameRow sameRow'
    carrier_respects_equiv := by
      intro row row' same sourceRow
      exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
  }
  exact {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SemiringLedger_additive_multiplicative_obligation_surface [AskSetup]
    [PackageSetup]
    {additive multiplicative shared distributive annihilation transport route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringLedger additive multiplicative shared distributive annihilation transport route
        endpoint bundle pkg ->
      UnaryHistory additive ∧ UnaryHistory multiplicative ∧ UnaryHistory shared ∧
        hsame shared (append additive multiplicative) ∧ Cont additive multiplicative shared ∧
          PkgSig bundle endpoint pkg := by
  intro ledger
  obtain ⟨additiveUnary, multiplicativeUnary, sharedUnary, _distributiveUnary,
    _annihilationUnary, _transportUnary, _routeUnary, _endpointUnary, sharedRow,
    _transportRow, _routeRow, _endpointRow, pkgRow⟩ := ledger
  exact ⟨additiveUnary, multiplicativeUnary, sharedUnary, sharedRow, sharedRow, pkgRow⟩

def SemiringDistributiveLedger (add mul left right dist : BHist) : Prop :=
  UnaryHistory add ∧
    UnaryHistory mul ∧
      Cont mul add left ∧
        Cont add mul right ∧
          hsame dist (append left right)

theorem SemiringDistributiveLedger_boundary {add mul left right dist : BHist} :
    SemiringDistributiveLedger add mul left right dist →
      UnaryHistory left ∧
        UnaryHistory right ∧
          UnaryHistory dist ∧
            hsame dist (append left right) ∧ Cont mul add left ∧ Cont add mul right := by
  intro ledger
  have leftUnary : UnaryHistory left :=
    unary_cont_closed ledger.right.left ledger.left ledger.right.right.left
  have rightUnary : UnaryHistory right :=
    unary_cont_closed ledger.left ledger.right.left ledger.right.right.right.left
  have distUnary : UnaryHistory dist :=
    unary_transport_symm
      (unary_cont_closed leftUnary rightUnary (cont_intro rfl))
      ledger.right.right.right.right
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro distUnary
        (And.intro ledger.right.right.right.right
          (And.intro ledger.right.right.left ledger.right.right.right.left))))

def SemiringFiniteSource [AskSetup] [PackageSetup]
    (add mul shared distrib annihil transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory add ∧ UnaryHistory mul ∧ UnaryHistory shared ∧ UnaryHistory distrib ∧
    UnaryHistory annihil ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont add mul shared ∧
        Cont shared distrib transport ∧ Cont annihil transport routes ∧
          Cont routes provenance name ∧ PkgSig bundle name pkg

theorem SemiringFiniteSource_semantic_name_certificate [AskSetup] [PackageSetup]
    {add mul shared distrib annihil transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        hsame := by
  intro source
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name (And.intro source (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows rowSource
        exact And.intro rowSource.left (hsame_trans (hsame_symm sameRows) rowSource.right)
    }
    pattern_sound := by
      intro _row rowSource
      exact rowSource
    ledger_sound := by
      intro _row rowSource
      exact rowSource
  }

theorem SemiringFiniteSource_concrete_history_instance [AskSetup] [PackageSetup]
    {add mul shared distrib annihil transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
        bundle pkg ->
      UnaryHistory add ∧ UnaryHistory mul ∧ UnaryHistory shared ∧ UnaryHistory distrib ∧
        UnaryHistory annihil ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory name ∧ Cont add mul shared ∧
            Cont shared distrib transport ∧ Cont annihil transport routes ∧
              Cont routes provenance name ∧ PkgSig bundle name pkg ∧
                SemanticNameCert
                  (fun row : BHist =>
                    SemiringFiniteSource add mul shared distrib annihil transport routes
                        provenance name bundle pkg ∧ hsame row name)
                  (fun row : BHist =>
                    SemiringFiniteSource add mul shared distrib annihil transport routes
                        provenance name bundle pkg ∧ hsame row name)
                  (fun row : BHist =>
                    SemiringFiniteSource add mul shared distrib annihil transport routes
                        provenance name bundle pkg ∧ hsame row name)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro source
  have sourceWitness := source
  obtain ⟨addUnary, mulUnary, sharedUnary, distribUnary, annihilUnary, transportUnary,
    routesUnary, provenanceUnary, nameUnary, sharedRoute, transportRoute, routesRoute,
    nameRoute, namePkg⟩ := source
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
              bundle pkg ∧ hsame row name)
        hsame :=
    SemiringFiniteSource_semantic_name_certificate sourceWitness
  exact
    ⟨addUnary, mulUnary, sharedUnary, distribUnary, annihilUnary, transportUnary, routesUnary,
      provenanceUnary, nameUnary, sharedRoute, transportRoute, routesRoute, nameRoute, namePkg,
      cert⟩

def SemiringZeroAnnihilationLedger (zero mul left right : BHist) : Prop :=
  UnaryHistory zero ∧ UnaryHistory mul ∧ Cont zero mul left ∧ Cont mul zero right

theorem SemiringZeroAnnihilationLedger_scope {zero mul left right : BHist} :
    SemiringZeroAnnihilationLedger zero mul left right ->
      UnaryHistory left ∧ UnaryHistory right ∧ hsame left (append zero mul) ∧
        hsame right (append mul zero) := by
  intro ledger
  obtain ⟨zeroUnary, mulUnary, leftRoute, rightRoute⟩ := ledger
  have leftUnary : UnaryHistory left :=
    unary_cont_closed zeroUnary mulUnary leftRoute
  have rightUnary : UnaryHistory right :=
    unary_cont_closed mulUnary zeroUnary rightRoute
  exact ⟨leftUnary, rightUnary, leftRoute, rightRoute⟩

theorem SemiringUp_StdBridge [AskSetup] [PackageSetup]
    {add mul shared distrib annihil transport routes provenance name bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemiringFiniteSource add mul shared distrib annihil transport routes provenance name bundle
        pkg ->
      Cont name provenance bridge ->
        PkgSig bundle bridge pkg ->
          SemanticNameCert
              (fun row : BHist =>
                SemiringFiniteSource add mul shared distrib annihil transport routes provenance
                    name bundle pkg ∧ hsame row bridge)
              (fun row : BHist =>
                hsame row add ∨ hsame row mul ∨ hsame row shared ∨ hsame row distrib ∨
                  hsame row annihil ∨ hsame row bridge)
              (fun row : BHist => hsame row bridge ∧ PkgSig bundle bridge pkg)
              hsame ∧
            UnaryHistory bridge ∧ Cont name provenance bridge ∧ PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro source nameProvenanceBridge bridgePkg
  have sourceWitness := source
  obtain ⟨_addUnary, _mulUnary, _sharedUnary, _distribUnary, _annihilUnary,
    _transportUnary, _routesUnary, provenanceUnary, nameUnary, _sharedRow, _transportRow,
    _routesRow, _nameRow, _namePkg⟩ := source
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed nameUnary provenanceUnary nameProvenanceBridge
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            SemiringFiniteSource add mul shared distrib annihil transport routes provenance name
                bundle pkg ∧ hsame row bridge)
          (fun row : BHist =>
            hsame row add ∨ hsame row mul ∨ hsame row shared ∨ hsame row distrib ∨
              hsame row annihil ∨ hsame row bridge)
          (fun row : BHist => hsame row bridge ∧ PkgSig bundle bridge pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridge (And.intro sourceWitness (hsame_refl bridge))
      equiv_refl := by
        intro row _rowSource
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows rowSource
        exact And.intro rowSource.left (hsame_trans (hsame_symm sameRows) rowSource.right)
    }
    pattern_sound := by
      intro _row rowSource
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rowSource.right))))
    ledger_sound := by
      intro _row rowSource
      exact ⟨rowSource.right, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary, nameProvenanceBridge, bridgePkg⟩

end BEDC.Derived.SemiringUp
