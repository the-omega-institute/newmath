import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SorgenfreyPlaneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SorgenfreyPlaneCarrier [AskSetup] [PackageSetup]
    (LX LY Q OX OY B S H C R N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
  Prop :=
  UnaryHistory LX ∧ UnaryHistory LY ∧ UnaryHistory Q ∧ UnaryHistory OX ∧
    UnaryHistory OY ∧ UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory R ∧ UnaryHistory N ∧ Cont LX LY Q ∧
        Cont OX OY B ∧ Cont B S C ∧ PkgSig bundle R pkg ∧ PkgSig bundle N pkg ∧
          hsame N S

inductive SorgenfreyPlaneRowSource
    (LX LY Q OX OY B S H C R N : BHist) : BHist -> Prop where
  | leftLine : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N LX
  | rightLine : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N LY
  | productTopology : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N Q
  | xTopology : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N OX
  | yTopology : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N OY
  | rectangleLedger : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N B
  | observableOpen : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N S
  | transport : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N H
  | replay : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N C
  | provenance : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N R
  | name : SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N N

theorem SorgenfreyPlaneNamecertObligations [AskSetup] [PackageSetup]
    {LX LY Q OX OY B S H C R N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SorgenfreyPlaneCarrier LX LY Q OX OY B S H C R N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N row)
          (fun row : BHist => SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N row)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle R pkg)
          hsame ∧
        Cont LX LY Q ∧ Cont OX OY B ∧ Cont B S C ∧ PkgSig bundle R pkg ∧
          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨lxUnary, lyUnary, qUnary, oxUnary, oyUnary, bUnary, sUnary, hUnary, cUnary,
    rUnary, nUnary, lineProduct, topologyRectangle, rectangleReplay, pkgRow, namePkg,
    _nameObservable⟩ :=
      carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N row)
          (fun row : BHist => SorgenfreyPlaneRowSource LX LY Q OX OY B S H C R N row)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle R pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro N SorgenfreyPlaneRowSource.name
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
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro row source
      cases source with
      | leftLine =>
          exact ⟨lxUnary, pkgRow⟩
      | rightLine =>
          exact ⟨lyUnary, pkgRow⟩
      | productTopology =>
          exact ⟨qUnary, pkgRow⟩
      | xTopology =>
          exact ⟨oxUnary, pkgRow⟩
      | yTopology =>
          exact ⟨oyUnary, pkgRow⟩
      | rectangleLedger =>
          exact ⟨bUnary, pkgRow⟩
      | observableOpen =>
          exact ⟨sUnary, pkgRow⟩
      | transport =>
          exact ⟨hUnary, pkgRow⟩
      | replay =>
          exact ⟨cUnary, pkgRow⟩
      | provenance =>
          exact ⟨rUnary, pkgRow⟩
      | name =>
          exact ⟨nUnary, pkgRow⟩
  }
  exact ⟨cert, lineProduct, topologyRectangle, rectangleReplay, pkgRow, namePkg⟩

end BEDC.Derived.SorgenfreyPlaneUp
