/*
 * Copyright 2015-2016 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language

import ca.uwaterloo.flix.language.ast.SourceLocation
import ca.uwaterloo.flix.language.ast.shared.Source
import ca.uwaterloo.flix.util.Formatter

/**
  * A common super-type for compilation messages.
  */
trait CompilationMessage {

  /**
    * Returns the kind of error message, e.g. "Syntax Error" or "Type Error".
    */
  def kind: CompilationMessageKind

  /**
    * Returns the input source of the error message.
    */
  def source: Source = loc.source

  /**
    * Returns the primary source location of the error.
    */
  def loc: SourceLocation

  /**
    * Returns additional locations associated with the error.
    */
  def locs: List[SourceLocation] = Nil

  /**
    * Returns a short description of the error message.
    */
  def summary: String

  /**
    * Returns the error message.
    *
    * You probably want to use [[messageWithLoc]] instead.
    */
  def message(formatter: Formatter): String

  /**
    * Returns a formatted string with helpful suggestions.
    */
  def explain(formatter: Formatter): Option[String] = None

  /**
    * Returns the error message formatted with source location.
    */
  def messageWithLoc(formatter: Formatter): String = {
    formatter.line(kind.toString, source.name) + System.lineSeparator() + message(formatter)
  }

  /**
    * Returns the given message `m` but with a URL linking to the source code of the error on GitHub.
    */
  protected def messageWithLink(m: String)(implicit f: sourcecode.FullName, l: sourcecode.Line): String = {
    // Assumes that flix.dev is configured with:
    //   location ~ ^/go/(.*)$ {
    //     return 301 https://github.com/flix/flix/edit/master/main/src/ca/uwaterloo/flix/$1;
    //   }
    val base = "https://flix.dev/go"

    // We convert the Java name:
    //   "ca.uwaterloo.flix.language.errors.ResolutionError.UndefinedName.message"
    // to:
    //   "language/errors/ResolutionError.scala"
    val file = f.value.split('.').drop(3).dropRight(2).mkString("/") + ".scala"
    val line = l.value
    val url = s"$base/$file#L$line"

    s"""$m
       |~ Want to help improve this error message? Create a PR on GitHub:
       |  $url
       |""".stripMargin
  }

}
