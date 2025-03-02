-- import Game.Levels.DemoWorld
import Game.Levels.World_one
import Game.Levels.World_two
import Game.Levels.World_three

-- Here's what we'll put on the title screen
Title "Rubik Cube Game"
Introduction
"
The Rubik's Cube Game is a mathematically formalized educational game designed to guide beginners through a series of interactive challenges, helping them learn foundational formal methods while uncovering the mathematical principles behind solving the Rubik's Cube. By combining problem-solving with mathematical theory, it offers an engaging way to master both formal logic and the cube's intricate mechanics.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use markdown.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
