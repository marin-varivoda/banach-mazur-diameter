import BMLean.Tables
import BMLean.Data.Hub015

namespace BMC

theorem hubOk_015 : hubChunkOk (parseRows BMD.hub015) = true := by native_decide

end BMC
