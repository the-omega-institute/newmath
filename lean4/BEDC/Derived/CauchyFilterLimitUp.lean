import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterLimitCarrier [AskSetup] [PackageSetup]
    (basis filter window readback tolerance sealRow transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory basis ∧ UnaryHistory filter ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory tolerance ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont basis filter window ∧ Cont window readback tolerance ∧
          Cont tolerance sealRow transport ∧ Cont transport route provenance ∧
            Cont sealRow provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem CauchyFilterLimitCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {basis filter window readback tolerance sealRow transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
              provenance name bundle pkg ∧ hsame row sealRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem CauchyFilterLimitCarrier_regular_seal_handoff [AskSetup] [PackageSetup]
    {basis filter window readback tolerance sealRow transport route provenance name consumerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
        provenance name bundle pkg ->
      Cont sealRow name consumerRead ->
        UnaryHistory basis ∧ UnaryHistory filter ∧ UnaryHistory window ∧
          UnaryHistory readback ∧ UnaryHistory tolerance ∧ UnaryHistory sealRow ∧
            UnaryHistory name ∧ UnaryHistory consumerRead ∧ Cont basis filter window ∧
              Cont window readback tolerance ∧ Cont tolerance sealRow transport ∧
                Cont sealRow name consumerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealNameConsumer
  obtain ⟨basisUnary, filterUnary, windowUnary, readbackUnary, toleranceUnary,
    sealRowUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    basisFilterWindow, windowReadbackTolerance, toleranceSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, namePkg⟩ := carrier
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealRowUnary nameUnary sealNameConsumer
  exact
    ⟨basisUnary, filterUnary, windowUnary, readbackUnary, toleranceUnary, sealRowUnary,
      nameUnary, consumerReadUnary, basisFilterWindow, windowReadbackTolerance,
      toleranceSealTransport, sealNameConsumer, provenancePkg, namePkg⟩

theorem CauchyFilterLimitCarrier_directed_net_handoff [AskSetup] [PackageSetup]
    {basis filter window readback tolerance sealRow transport route provenance name directed tail
      convergence directedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterLimitCarrier basis filter window readback tolerance sealRow transport route
        provenance name bundle pkg ->
      UnaryHistory directed ->
        Cont basis directed tail ->
          Cont tail route convergence ->
            Cont convergence sealRow directedRead ->
              PkgSig bundle directedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row directedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row basis ∨ hsame row filter ∨ hsame row window ∨
                        hsame row readback ∨ hsame row tolerance ∨ hsame row sealRow ∨
                          Cont convergence sealRow directedRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle directedRead pkg ∧
                        hsame row directedRead)
                    hsame ∧
                  UnaryHistory tail ∧ UnaryHistory convergence ∧ UnaryHistory directedRead ∧
                    Cont basis directed tail ∧ Cont tail route convergence ∧
                      Cont convergence sealRow directedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier directedUnary basisDirectedTail tailRouteConvergence convergenceSealDirected
    directedPkg
  obtain ⟨basisUnary, _filterUnary, _windowUnary, _readbackUnary, _toleranceUnary,
    sealRowUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    _basisFilterWindow, _windowReadbackTolerance, _toleranceSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed basisUnary directedUnary basisDirectedTail
  have convergenceUnary : UnaryHistory convergence :=
    unary_cont_closed tailUnary routeUnary tailRouteConvergence
  have directedReadUnary : UnaryHistory directedRead :=
    unary_cont_closed convergenceUnary sealRowUnary convergenceSealDirected
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row directedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basis ∨ hsame row filter ∨ hsame row window ∨ hsame row readback ∨
              hsame row tolerance ∨ hsame row sealRow ∨
                Cont convergence sealRow directedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle directedRead pkg ∧
              hsame row directedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro directedRead
        ⟨hsame_refl directedRead, directedReadUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr convergenceSealDirected)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, directedPkg, source.left⟩
  }
  exact
    ⟨cert, tailUnary, convergenceUnary, directedReadUnary, basisDirectedTail,
      tailRouteConvergence, convergenceSealDirected⟩

end BEDC.Derived.CauchyFilterLimitUp
