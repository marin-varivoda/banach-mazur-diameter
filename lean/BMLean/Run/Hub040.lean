import BMLean.Tables
import BMLean.Data.Hub040

namespace BMC

theorem hubOk_040 : hubChunkOk (parseRows BMD.hub040) = true := by native_decide

end BMC
