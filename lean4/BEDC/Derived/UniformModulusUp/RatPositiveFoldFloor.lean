import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_rat_positive_fold_floor [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow center floorRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      Cont bundleRow radius center →
        Cont precision radius foldLedger →
          Cont center foldLedger floorRead →
            Cont floorRead nameRow exported →
              PkgSig bundle exported pkg →
                UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory center ∧
                  UnaryHistory foldLedger ∧ UnaryHistory floorRead ∧ UnaryHistory exported ∧
                    Cont bundleRow radius center ∧ Cont precision radius foldLedger ∧
                      Cont center foldLedger floorRead ∧ Cont floorRead nameRow exported ∧
                        PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro packet bundleRadiusCenter precisionRadiusFold centerFoldFloor floorNameExport exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, _packetFoldRoute, _provenanceRoute, _packetPkg⟩ :=
    packet
  have centerUnary : UnaryHistory center :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCenter
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFold
  have floorReadUnary : UnaryHistory floorRead :=
    unary_cont_closed centerUnary foldLedgerUnary centerFoldFloor
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed floorReadUnary nameRowUnary floorNameExport
  exact
    ⟨precisionUnary, radiusUnary, centerUnary, foldLedgerUnary, floorReadUnary,
      exportedUnary, bundleRadiusCenter, precisionRadiusFold, centerFoldFloor,
      floorNameExport, exportPkg⟩

end BEDC.Derived.UniformModulusUp
