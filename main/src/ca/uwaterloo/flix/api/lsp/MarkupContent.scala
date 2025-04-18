/*
 * Copyright 2020 Magnus Madsen
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
package ca.uwaterloo.flix.api.lsp

import org.eclipse.lsp4j
import org.json4s.JsonDSL.*
import org.json4s.*

/**
  * Represents a `MarkupContent` in LSP.
  *
  * @param kind  The type of the Markup.
  * @param value The content itself.
  */
case class MarkupContent(kind: MarkupKind, value: String) {
  def toJSON: JValue = ("kind" -> kind.toJSON) ~ ("value" -> value)

  def toLsp4j: lsp4j.MarkupContent = {
    val markupContent = new lsp4j.MarkupContent()
    markupContent.setKind(kind.toLsp4j)
    markupContent.setValue(value)
    markupContent
  }
}
