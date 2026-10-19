import BMLean.Tables
import BMLean.Data.Hub059

namespace BMC

theorem hubOk_059 : hubChunkOk (parseRows BMD.hub059) = true := by native_decide

end BMC
