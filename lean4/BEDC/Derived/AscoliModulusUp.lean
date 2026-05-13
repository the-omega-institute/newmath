import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AscoliModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AscoliModulusPacket [AskSetup] [PackageSetup]
    (source target family tolerance radius probe stability equicontinuity uniformRows
      transport routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory family ∧
    UnaryHistory tolerance ∧ UnaryHistory radius ∧ UnaryHistory probe ∧
      UnaryHistory stability ∧ UnaryHistory equicontinuity ∧ UnaryHistory uniformRows ∧
        UnaryHistory nameRow ∧ Cont tolerance radius equicontinuity ∧
          Cont family radius uniformRows ∧ Cont equicontinuity uniformRows transport ∧
            Cont transport routes provenance ∧ PkgSig bundle provenance pkg

theorem AscoliModulusPacket_equicontinuity_ledger [AskSetup] [PackageSetup]
    {source target family tolerance radius probe stability equicontinuity uniformRows
      transport routes provenance nameRow source' target' family' tolerance' radius'
      equicontinuity' uniformRows' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AscoliModulusPacket source target family tolerance radius probe stability
        equicontinuity uniformRows transport routes provenance nameRow bundle pkg ->
      hsame source source' ->
        hsame target target' ->
          hsame family family' ->
            hsame tolerance tolerance' ->
              hsame radius radius' ->
                Cont tolerance' radius' equicontinuity' ->
                  Cont family' radius' uniformRows' ->
                    AscoliModulusPacket source' target' family' tolerance' radius' probe
                        stability equicontinuity' uniformRows' transport routes provenance
                        nameRow bundle pkg ∧
                      hsame equicontinuity equicontinuity' ∧
                        hsame uniformRows uniformRows' := by
  intro packet sameSource sameTarget sameFamily sameTolerance sameRadius
    equicontinuityCont' uniformRowsCont'
  obtain ⟨sourceUnary, targetUnary, familyUnary, toleranceUnary, radiusUnary, probeUnary,
    stabilityUnary, _equicontinuityUnary, _uniformRowsUnary, nameUnary, equicontinuityCont,
    uniformRowsCont, transportCont, provenanceCont, pkgSig⟩ := packet
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have targetUnary' : UnaryHistory target' :=
    unary_transport targetUnary sameTarget
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have equicontinuityUnary' : UnaryHistory equicontinuity' :=
    unary_cont_closed toleranceUnary' radiusUnary' equicontinuityCont'
  have uniformRowsUnary' : UnaryHistory uniformRows' :=
    unary_cont_closed familyUnary' radiusUnary' uniformRowsCont'
  have sameEquicontinuity : hsame equicontinuity equicontinuity' :=
    cont_respects_hsame sameTolerance sameRadius equicontinuityCont equicontinuityCont'
  have sameUniformRows : hsame uniformRows uniformRows' :=
    cont_respects_hsame sameFamily sameRadius uniformRowsCont uniformRowsCont'
  have transportCont' : Cont equicontinuity' uniformRows' transport := by
    cases sameEquicontinuity
    cases sameUniformRows
    exact transportCont
  exact
    ⟨⟨sourceUnary', targetUnary', familyUnary', toleranceUnary', radiusUnary', probeUnary,
      stabilityUnary, equicontinuityUnary', uniformRowsUnary', nameUnary, equicontinuityCont',
      uniformRowsCont', transportCont', provenanceCont, pkgSig⟩, sameEquicontinuity,
      sameUniformRows⟩

theorem AscoliModulusPacket_arzela_ascoli_handoff [AskSetup] [PackageSetup]
    {source target family tolerance radius probe stability equicontinuity uniformRows
      transport routes provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AscoliModulusPacket source target family tolerance radius probe stability
        equicontinuity uniformRows transport routes provenance nameRow bundle pkg ->
      UnaryHistory equicontinuity ∧ UnaryHistory uniformRows ∧ UnaryHistory transport ∧
        Cont tolerance radius equicontinuity ∧ Cont family radius uniformRows ∧
          Cont equicontinuity uniformRows transport ∧ Cont transport routes provenance ∧
            PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, _toleranceUnary, _radiusUnary, _probeUnary,
    _stabilityUnary, equicontinuityUnary, uniformRowsUnary, _nameUnary, equicontinuityCont,
    uniformRowsCont, transportCont, provenanceCont, pkgSig⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed equicontinuityUnary uniformRowsUnary transportCont
  exact
    ⟨equicontinuityUnary, uniformRowsUnary, transportUnary, equicontinuityCont,
      uniformRowsCont, transportCont, provenanceCont, pkgSig⟩

theorem AscoliModulusPacket_finite_net_stability [AskSetup] [PackageSetup]
    {source target family tolerance radius probe stability equicontinuity uniformRows transport
      routes provenance nameRow stabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AscoliModulusPacket source target family tolerance radius probe stability equicontinuity
        uniformRows transport routes provenance nameRow bundle pkg ->
      Cont probe stability stabilityRead ->
        UnaryHistory probe ∧ UnaryHistory stability ∧ UnaryHistory stabilityRead ∧
          Cont probe stability stabilityRead ∧ PkgSig bundle provenance pkg := by
  intro packet stabilityRoute
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, _toleranceUnary, _radiusUnary, probeUnary,
    stabilityUnary, _equicontinuityUnary, _uniformRowsUnary, _nameUnary, _equicontinuityCont,
    _uniformRowsCont, _transportCont, _provenanceCont, pkgSig⟩ := packet
  have stabilityReadUnary : UnaryHistory stabilityRead :=
    unary_cont_closed probeUnary stabilityUnary stabilityRoute
  exact ⟨probeUnary, stabilityUnary, stabilityReadUnary, stabilityRoute, pkgSig⟩

theorem AscoliModulusPacket_rational_radius_transport [AskSetup] [PackageSetup]
    {source target family tolerance radius probe stability equicontinuity uniformRows
      transport routes provenance nameRow radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AscoliModulusPacket source target family tolerance radius probe stability equicontinuity
        uniformRows transport routes provenance nameRow bundle pkg ->
      Cont tolerance radius radiusRead ->
        PkgSig bundle radiusRead pkg ->
          UnaryHistory tolerance ∧ UnaryHistory radius ∧ UnaryHistory radiusRead ∧
            Cont tolerance radius equicontinuity ∧ Cont tolerance radius radiusRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet toleranceRadiusRead radiusReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _familyUnary, toleranceUnary, radiusUnary, _probeUnary,
    _stabilityUnary, _equicontinuityUnary, _uniformRowsUnary, _nameUnary,
    toleranceRadiusEquicontinuity, _familyRadiusUniformRows, _transportCont,
    _provenanceCont, provenancePkg⟩ := packet
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed toleranceUnary radiusUnary toleranceRadiusRead
  exact
    ⟨toleranceUnary, radiusUnary, radiusReadUnary, toleranceRadiusEquicontinuity,
      toleranceRadiusRead, provenancePkg, radiusReadPkg⟩

end BEDC.Derived.AscoliModulusUp
