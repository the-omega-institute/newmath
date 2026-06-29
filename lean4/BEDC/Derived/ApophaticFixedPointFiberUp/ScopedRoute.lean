import BEDC.Derived.ApophaticFixedPointFiberUp.TasteGate

namespace BEDC.Derived.ApophaticFixedPointFiberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticFixedPointFiber_scoped_route [AskSetup] [PackageSetup]
    {digest socket gap boundary inscription transport routes provenance name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg →
      UnaryHistory boundary →
        Cont inscription transport scopedRead →
          PkgSig bundle scopedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                    hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                      hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription
                      transport routes provenance name bundle pkg ∧
                      Cont digest socket gap ∧ Cont gap boundary inscription ∧
                        Cont inscription transport scopedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle scopedRead pkg)
                hsame ∧
              UnaryHistory gap ∧ UnaryHistory inscription ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryUnary scopedRoute scopedPkg
  have carrierWitness :
      ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg := carrier
  obtain ⟨digestUnary, socketUnary, transportUnary, _provenanceUnary, digestSocketGap,
    gapBoundaryInscription, _inscriptionTransportRoutes, provenancePkg, namePkg⟩ := carrier
  have gapUnary : UnaryHistory gap :=
    unary_cont_closed digestUnary socketUnary digestSocketGap
  have inscriptionUnary : UnaryHistory inscription :=
    unary_cont_closed gapUnary boundaryUnary gapBoundaryInscription
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed inscriptionUnary transportUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row digest ∨ hsame row socket ∨ hsame row gap ∨ hsame row boundary ∨
              hsame row inscription ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              ApophaticFixedPointFiberCarrier digest socket gap boundary inscription
                transport routes provenance name bundle pkg ∧
                Cont digest socket gap ∧ Cont gap boundary inscription ∧
                  Cont inscription transport scopedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierWitness, digestSocketGap, gapBoundaryInscription, scopedRoute,
          provenancePkg, namePkg, scopedPkg⟩
  }
  exact ⟨cert, gapUnary, inscriptionUnary, scopedUnary⟩

end BEDC.Derived.ApophaticFixedPointFiberUp
