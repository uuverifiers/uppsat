package uppsat

import scalafx.Includes._
import scalafx.application.JFXApp
import scalafx.application.JFXApp.PrimaryStage
import scalafx.event.ActionEvent
import scalafx.geometry.Insets
import scalafx.scene.Scene
import scalafx.scene.control.TextFormatter.Change
import scalafx.scene.control.{Label, TextArea, TextField, TextFormatter}
import scalafx.scene.layout.{BorderPane, VBox}
import scalafx.util.StringConverter


object test {
  def things() = {
    println("Hejsan\n")
    println("...")
  }

  def stuff() = {
    val (res, buffer) = captureOutput(things())
    println("Hmm")
  }


  def captureOutput[A](computation : => A) : (A, String) = {
    val buffer = new java.io.ByteArrayOutputStream
    val res = Console.withOut(buffer) (computation)
    (res, buffer.toString)
  }
}

object TextFormatterWithChangeFilterDemo extends JFXApp {
 
  case class Message(text: String) {
    override def toString = '"' + text + '"'
  }
 
  val prompt = "> "
 
  val converter = new StringConverter[Message] {
    override def fromString(s: String): Message = {
      val r =
        if (s.startsWith(prompt)) s.substring(prompt.length)
        else s
      Message(r)
    }
    override def toString(v: Message): String = {
      prompt + v.text
    }
  }
 

 
  val outputTextArea = new TextArea {
    editable = false
    focusTraversable = false
  }
 
  val textField = new TextField {
    text = prompt
    onAction = (a: ActionEvent) => {
      val str = text()
      val args = str.split("\\s+")
      outputTextArea.text = "Running: " + str + '\n' + outputTextArea.text()
      text() = ""
      val result = UppSAT.main_aux(args)
      outputTextArea.text = "Result: " + result + '\n' + outputTextArea.text()
    }
  }
 
  stage = new PrimaryStage {
    scene = new Scene(300, 200) {
      title = "TextFormatter Demo"
      root = new VBox {
        spacing = 6
        padding = Insets(10)
        children = Seq(
          new BorderPane {
            top = textField
            center = outputTextArea
          }
        )
      }
    }
  }
}
