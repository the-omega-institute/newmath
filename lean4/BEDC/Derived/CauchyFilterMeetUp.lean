import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterMeetCarrier [AskSetup] [PackageSetup]
    (uniformRow filterLeft filterRight basisLeft basisRight refineRow windowRow regularRow
      toleranceRow limitRow sealRow transportRow routeRow provenanceRow certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory uniformRow ∧ UnaryHistory filterLeft ∧ UnaryHistory filterRight ∧
    UnaryHistory basisLeft ∧ UnaryHistory basisRight ∧ UnaryHistory refineRow ∧
      UnaryHistory windowRow ∧ UnaryHistory regularRow ∧ UnaryHistory toleranceRow ∧
        UnaryHistory limitRow ∧ UnaryHistory sealRow ∧ UnaryHistory transportRow ∧
          UnaryHistory routeRow ∧ UnaryHistory provenanceRow ∧ UnaryHistory certRow ∧
            Cont uniformRow filterLeft basisLeft ∧
              Cont uniformRow filterRight basisRight ∧
                Cont basisLeft basisRight refineRow ∧
                  Cont refineRow windowRow regularRow ∧
                    Cont regularRow toleranceRow limitRow ∧
                      Cont limitRow sealRow transportRow ∧
                        Cont transportRow routeRow provenanceRow ∧
                          Cont provenanceRow certRow sealRow ∧
                            PkgSig bundle provenanceRow pkg ∧ PkgSig bundle certRow pkg

theorem CauchyFilterMeetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {uniformRow filterLeft filterRight basisLeft basisRight refineRow windowRow regularRow
      toleranceRow limitRow sealRow transportRow routeRow provenanceRow certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterMeetCarrier uniformRow filterLeft filterRight basisLeft basisRight refineRow
        windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow provenanceRow
        certRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterMeetCarrier uniformRow filterLeft filterRight basisLeft basisRight
              refineRow windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow
              provenanceRow certRow bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyFilterMeetCarrier uniformRow filterLeft filterRight basisLeft basisRight
              refineRow windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow
              provenanceRow certRow bundle pkg ∧
            (hsame row refineRow ∨ hsame row limitRow ∨ hsame row sealRow))
        (fun row : BHist =>
          CauchyFilterMeetCarrier uniformRow filterLeft filterRight basisLeft basisRight
              refineRow windowRow regularRow toleranceRow limitRow sealRow transportRow routeRow
              provenanceRow certRow bundle pkg ∧
            hsame row sealRow ∧ PkgSig bundle provenanceRow pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_uniformUnary, _filterLeftUnary, _filterRightUnary, _basisLeftUnary,
    _basisRightUnary, _refineUnary, _windowUnary, _regularUnary, _toleranceUnary, _limitUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _uniformLeft,
    _uniformRight, _basisRefine, _refineRegular, _regularLimit, _limitTransport,
    _transportProvenance, _provenanceSeal, provenancePkg, _certPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrierWitness (hsame_refl sealRow))
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
      exact And.intro sourceRow.left (Or.inr (Or.inr sourceRow.right))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left (And.intro sourceRow.right provenancePkg)
  }

end BEDC.Derived.CauchyFilterMeetUp
