import BMLean.Tables
import BMLean.Data.Hub005

namespace BMC

theorem hubOk_005 : hubChunkOk (parseRows BMD.hub005) = true := by native_decide

end BMC
