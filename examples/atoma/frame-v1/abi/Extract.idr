module Extract

import FrameAbi

%default total

main : IO ()
main = putStr (encode frameParse)
