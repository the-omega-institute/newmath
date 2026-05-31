import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AuthorizedGeneratorRecursorDisplayedRoute [AskSetup] [PackageSetup]
    (authorization generator fuel route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory authorization ∧ UnaryHistory generator ∧ UnaryHistory fuel ∧
    UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      Cont authorization generator route ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem AuthorizedGeneratorRecursor_ledger_exhaustion [AskSetup] [PackageSetup]
    {authorization generator fuel route provenance name output : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route provenance name
        bundle pkg ->
      Cont fuel route output ->
        PkgSig bundle output pkg ->
          SemanticNameCert
              (fun row : BHist =>
                AuthorizedGeneratorRecursorDisplayedRoute authorization generator fuel route
                    provenance name bundle pkg ∧ hsame row output)
              (fun row : BHist =>
                UnaryHistory authorization ∧ UnaryHistory generator ∧ UnaryHistory fuel ∧
                  UnaryHistory route ∧ hsame row output)
              (fun _row : BHist =>
                Cont authorization generator route ∧ Cont fuel route output ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle output pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro displayed fuelRoute outputPkg
  have displayedWitness := displayed
  obtain ⟨authorizationUnary, generatorUnary, fuelUnary, routeUnary, _provenanceUnary,
    _nameUnary, authorizationGeneratorRoute, provenancePkg, _namePkg⟩ := displayed
  have outputUnary : UnaryHistory output :=
    unary_cont_closed fuelUnary routeUnary fuelRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro output
        (And.intro displayedWitness (hsame_refl output))
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
        intro _row _other sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨authorizationUnary, generatorUnary, fuelUnary, routeUnary, sourceRow.right⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨authorizationGeneratorRoute, fuelRoute, provenancePkg, outputPkg⟩
  }

theorem AuthorizedGeneratorRecursorDisplayedRoute_downstream_coverage [AskSetup] [PackageSetup]
    {A G F K P N branchRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A G branchRead ->
      Cont F K outputRead ->
        PkgSig bundle P pkg ->
          PkgSig bundle N pkg ->
            UnaryHistory A ->
              UnaryHistory G ->
                UnaryHistory F ->
                  UnaryHistory K ->
                    UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                      Cont A G branchRead ∧ Cont F K outputRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro branchRoute outputRoute provenancePkg namePkg authorizationUnary generatorUnary fuelUnary
    continuationUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed authorizationUnary generatorUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed fuelUnary continuationUnary outputRoute
  exact
    ⟨branchReadUnary, outputReadUnary, branchRoute, outputRoute, provenancePkg, namePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
