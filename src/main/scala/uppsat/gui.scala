package uppsat

import scalafx.Includes._
import scalafx.application.JFXApp
import scalafx.application.JFXApp.PrimaryStage
import scalafx.event.ActionEvent
import scalafx.geometry.Insets
import scalafx.scene.Scene
import scalafx.scene.control.TextFormatter.Change
import scalafx.scene.control.{CheckBox, Label, TextArea, TextField, TextFormatter}
import scalafx.scene.layout.{BorderPane, VBox, HBox}
import scalafx.util.StringConverter
import scalafx.scene.layout.VBox
import scalafx.scene.text.Text
import scalafx.scene.control.{RadioButton, ToggleGroup}
import scalafx.stage.FileChooser
import scalafx.stage.FileChooser.ExtensionFilter


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
      outputTextArea.text = outputTextArea.text() + '\n' + "Result: " + result
    }
  }

  val togApproximation = new ToggleGroup()
  val togBackend = new ToggleGroup()
  val togValidator = new ToggleGroup()    

  val radioApproximation = {
    val approxs = globalOptions.approximationDescriptions.keys
    for (a <- approxs) yield {
      new RadioButton {
        maxWidth = 200
        maxHeight = 50
        text = a
        selected = true
        toggleGroup = togApproximation
        onAction = (a: ActionEvent) => updateCmd()
      }
    }
  }

  val radioBackend = {
    val approxs = globalOptions.solverDescriptions.keys
    for (a <- approxs) yield {
      new RadioButton {
        maxWidth = 200
        maxHeight = 50
        text = a
        selected = true
        toggleGroup = togBackend
        onAction = (a: ActionEvent) => updateCmd()        
      }
    }    
  }

  val radioValidator = {
    val approxs = globalOptions.solverDescriptions.keys
    for (a <- approxs) yield {
      new RadioButton {
        maxWidth = 200
        maxHeight = 50
        text = a
        selected = true        
        toggleGroup = togValidator
        onAction = (a: ActionEvent) => updateCmd()        
      }
    }    
  }

  val checkDetailedApproximation = new CheckBox {
    text = "-a"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkVerbose = new CheckBox {
    text = "-v"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkStatistics = new CheckBox {
    text = "-s"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkModel = new CheckBox {
    text = "-m"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkDebug = new CheckBox {
    text = "-d"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkVerify = new CheckBox {
    text = "-p"
    onAction = (a: ActionEvent) => updateCmd()
  }

  val checkBoxes = Seq(checkDetailedApproximation, checkVerbose, checkStatistics, checkModel, checkDebug, checkVerify)

  def updateCmd() : Unit = {
    val backend = "-backend=" + radioBackend.filter(_.selected.value).head.text.value
    val validator = "-validator=" + radioValidator.filter(_.selected.value).head.text.value
    val approximation = "-app=" + radioApproximation.filter(_.selected.value).head.text.value

    val cbString = 
      (for (cb <- checkBoxes; if cb.selected.value) yield {
        cb.text.value
      }).mkString(" ")
    textField.text() = approximation + " " + backend + " " + validator + " " + cbString + " " + file
  }

    // println("\t -t=NUM - set a soft timeout in seconds. Soft means that timeout is checked between iterations only.")  

  stage = new PrimaryStage {
    scene = new Scene(300, 200) {
      title = "UppSAT"
      root = new VBox {
        spacing = 6
        padding = Insets(10)
        children = Seq(
          new BorderPane {
            bottom = textField
            center = outputTextArea
            top = new HBox {
              spacing = 50
              children = Seq(

                new VBox {
                  children = Seq(
                    new Text {
                      text = "Approximation"
                      style = "-fx-font: normal bold 32pt sans-serif"
                    }
                  ) ++ radioApproximation
                },

                new VBox {
                  children = Seq(
                    new Text {
                      text = "Backend"
                      style = "-fx-font: normal bold 32pt sans-serif"
                    }
                  ) ++ radioBackend
                },

                new VBox {
                  children = Seq(
                    new Text {
                      text = "Validator"
                      style = "-fx-font: normal bold 32pt sans-serif"
                    }
                  ) ++ radioValidator
                },

                new VBox {
                  children =
                    Seq(new Text {
                      text = "Options"
                      style = "-fx-font: normal bold 32pt sans-serif"
                    }) ++ checkBoxes
                }                
              )
            }
          }
        )
      }
    }
  }

  var file = ""

  def chooseFile() = {
    val fileChooser = new FileChooser {
      title = "Open Resource File"
      extensionFilters ++= Seq(
        new ExtensionFilter("SMT-LIB2", "*.smt2"),
        new ExtensionFilter("All Files", "*.*")
      )
    }
    val selectedFile = fileChooser.showOpenDialog(stage)
    if (selectedFile != null) {
      file = selectedFile.getPath()
      println(file)
    }
  }



  chooseFile()
  updateCmd()  
}
