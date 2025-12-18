module Main where

import Preload
import Concur.Dom (runWidgetInDom)
import Task.Script.Renderer as Renderer
import Task.Script.Example.Subsidy as Example

-- import Task.Script.Example.Deadline as Example
-- import Task.Script.Example.Singles as Example

-- import Test.Selection as Test
-- import Test.Tree as Test

main :: Effect Unit
-- main = runWidgetInDom "root" <| Test.main
main = runWidgetInDom "root" <| Renderer.main Example.world "request subsidy"
