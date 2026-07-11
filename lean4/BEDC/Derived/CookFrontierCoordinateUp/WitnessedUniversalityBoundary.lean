import BEDC.Derived.CookFrontierCoordinateUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CookFrontierCoordinateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CookFrontierCoordinate_witnessed_universality_boundary
    {frontier scale sample audit failure transports routes provenance nameCert scaleRead
      sampleRead auditRead failureRead terminalRead : BHist} :
    TasteGate.cookFrontierCoordinateFields
        (TasteGate.CookFrontierCoordinateUp.mk frontier scale sample audit failure transports
          routes provenance nameCert) =
      [frontier, scale, sample, audit, failure, transports, routes, provenance, nameCert] →
      Cont frontier scale scaleRead →
        Cont scaleRead sample sampleRead →
          Cont sampleRead audit auditRead →
            Cont auditRead failure failureRead →
              Cont failureRead routes terminalRead →
                hsame terminalRead
                  (append (append (append (append (append frontier scale) sample) audit)
                    failure) routes) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsExact routeScale routeSample routeAudit routeFailure routeTerminal
  cases routeScale
  cases routeSample
  cases routeAudit
  cases routeFailure
  cases routeTerminal
  rfl

end BEDC.Derived.CookFrontierCoordinateUp
