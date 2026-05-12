import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ComputableRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ComputableRealSourcePacket [AskSetup] [PackageSetup]
    (stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
    UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
      Cont transport routes provenance ∧ Cont provenance name endpoint ∧
        PkgSig bundle endpoint pkg

theorem ComputableRealSourcePacket_ledger_coverage [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
        UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
          Cont transport routes provenance ∧ Cont provenance name endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact packet.left
  · constructor
    · exact packet.right.left
    · constructor
      · exact packet.right.right.left
      · constructor
        · exact packet.right.right.right.left
        · constructor
          · exact packet.right.right.right.right.left
          · constructor
            · exact packet.right.right.right.right.right.left
            · constructor
              · exact packet.right.right.right.right.right.right.left
              · constructor
                · exact packet.right.right.right.right.right.right.right.left
                · constructor
                  · exact packet.right.right.right.right.right.right.right.right.left
                  · exact packet.right.right.right.right.right.right.right.right.right

def ComputableRealSource [AskSetup] [PackageSetup]
    (schedule modulus dyadic regular sealRow transport route provenance registration
      approximationWindow sealWindow packet : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory registration ∧
        Cont schedule modulus approximationWindow ∧ Cont regular sealRow sealWindow ∧
          Cont approximationWindow sealWindow packet ∧ PkgSig bundle packet pkg

theorem ComputableRealSource_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport route provenance registration
      approximationWindow sealWindow packet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSource schedule modulus dyadic regular sealRow transport route provenance
        registration approximationWindow sealWindow packet bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row packet ∧
            ComputableRealSource schedule modulus dyadic regular sealRow transport route
              provenance registration approximationWindow sealWindow row bundle pkg)
        (fun _row : BHist =>
          UnaryHistory packet ∧ Cont schedule modulus approximationWindow ∧
            Cont regular sealRow sealWindow)
        (fun _row : BHist =>
          PkgSig bundle packet pkg ∧ UnaryHistory provenance ∧ UnaryHistory registration)
        (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := by
  intro source
  have sourceProof := source
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary,
    transportUnary, routeUnary, provenanceUnary, registrationUnary, approximationRow,
    sealWindowCont, packetRow, packetSig⟩ := source
  have packetUnary : UnaryHistory packet :=
    unary_cont_closed (unary_cont_closed scheduleUnary modulusUnary approximationRow)
      (unary_cont_closed regularUnary sealUnary sealWindowCont) packetRow
  let SourceSpec : BHist -> Prop :=
    fun row : BHist =>
      hsame row packet ∧
        ComputableRealSource schedule modulus dyadic regular sealRow transport route provenance
          registration approximationWindow sealWindow row bundle pkg
  let PatternSpec : BHist -> Prop :=
    fun _row : BHist =>
      UnaryHistory packet ∧ Cont schedule modulus approximationWindow ∧
        Cont regular sealRow sealWindow
  let LedgerPolicy : BHist -> Prop :=
    fun _row : BHist =>
      PkgSig bundle packet pkg ∧ UnaryHistory provenance ∧ UnaryHistory registration
  let ClassifierSpec : BHist -> BHist -> Prop :=
    fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row'
  have packetSource : SourceSpec packet :=
    ⟨hsame_refl packet, sourceProof⟩
  have core : NameCert SourceSpec ClassifierSpec := {
    carrier_inhabited := Exists.intro packet packetSource
    equiv_refl := by
      intro row rowSource
      obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, _regularUnary, _sealUnary,
        _transportUnary, _routeUnary, _provenanceUnary, _registrationUnary,
        _approximationRow, _sealWindowCont, _packetRow, rowPkg⟩ := rowSource.right
      exact ⟨rowPkg, hsame_refl row⟩
    equiv_symm := by
      intro row row' classified
      cases classified.right
      exact ⟨classified.left, hsame_refl row⟩
    equiv_trans := by
      intro row row' row'' classifiedLeft classifiedRight
      exact ⟨classifiedLeft.left, hsame_trans classifiedLeft.right classifiedRight.right⟩
    carrier_respects_equiv := by
      intro row row' classified rowSource
      cases classified.right
      exact rowSource
  }
  exact {
    core := core
    pattern_sound := by
      intro _row _rowSource
      exact ⟨packetUnary, approximationRow, sealWindowCont⟩
    ledger_sound := by
      intro _row _rowSource
      exact ⟨packetSig, provenanceUnary, registrationUnary⟩
  }

end BEDC.Derived.ComputableRealUp
