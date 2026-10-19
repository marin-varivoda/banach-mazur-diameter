import BMLean.Tables
import BMLean.Data.Hub067

namespace BMC

theorem hubOk_067 : hubChunkOk (parseRows BMD.hub067) = true := by native_decide

end BMC
