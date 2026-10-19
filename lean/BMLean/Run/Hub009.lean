import BMLean.Tables
import BMLean.Data.Hub009

namespace BMC

theorem hubOk_009 : hubChunkOk (parseRows BMD.hub009) = true := by native_decide

end BMC
