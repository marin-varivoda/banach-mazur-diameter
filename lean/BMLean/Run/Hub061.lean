import BMLean.Tables
import BMLean.Data.Hub061

namespace BMC

theorem hubOk_061 : hubChunkOk (parseRows BMD.hub061) = true := by native_decide

end BMC
