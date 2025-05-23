/*
 *  Copyright 2024 Magnus Madsen
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

///
/// An effect used to read from the file system.
///
/// All operations on this effect are infallible.
/// If an operation fails the handler must deal with it.
///
pub eff FileRead {

    ///
    /// Returns `true` if the given file `f` exists.
    ///
    def exists(f: String): Bool

    ///
    /// Returns `true` is the given file `f` is a directory.
    ///
    def isDirectory(f: String): Bool

    ///
    /// Returns `true` if the given file `f` is a regular file.
    ///
    def isRegularFile(f: String): Bool

    ///
    /// Returns `true` if the given file `f` is readable.
    ///
    def isReadable(f: String): Bool

    ///
    /// Returns `true` if the given file `f` is a symbolic link.
    ///
    def isSymbolicLink(f: String): Bool

    ///
    /// Returns `true` if the given file `f` is writable.
    ///
    def isWritable(f: String): Bool

    ///
    /// Returns `true` if the given file `f` is executable.
    ///
    def isExecutable(f: String): Bool

    ///
    /// Returns the last access time of the given file `f` in milliseconds since the epoch.
    ///
    def accessTime(f: String): Int64

    ///
    /// Returns the creation time of the given file `f` in milliseconds since the epoch.
    ///
    def creationTime(f: String): Int64

    ///
    /// Returns the last-modified timestamp of the given file `f` in milliseconds since the epoch.
    ///
    def modificationTime(f: String): Int64

    ///
    /// Returns the size of the given file `f` in bytes.
    ///
    def size(f: String): Int64

    ///
    /// Returns a string of all lines in the given file `f`.
    ///
    def read(f: String): String

    ///
    /// Returns a list of all lines in the given file `f`.
    ///
    def readLines(f: String): List[String]

    ///
    /// Returns a vector of all the bytes in the given file `f`.
    ///
    def readBytes(f: String): Vector[Int8]

    ///
    /// Returns a list with the names of all files and directories in the given directory `d`.
    ///
    def list(f: String): List[String]

}

mod FileRead {

    import java.io.File
    import java.io.IOException
    import java.lang.Class
    import java.lang.{String => JString}
    import java.lang.UnsupportedOperationException
    import java.nio.file.attribute.BasicFileAttributes
    import java.nio.file.Files
    import java.nio.file.InvalidPathException
    import java.nio.file.LinkOption
    import java.nio.file.NotDirectoryException
    import java.nio.file.Path
    import java.nio.file.Paths

    use IoError.IoError
    use IoError.ErrorKind

    ///
    /// Handles the `FileRead` effect of the given function `f`.
    ///
    /// In other words, re-interprets the `FileRead` effect using the `IO` effect.
    ///
    pub def handle(f: a -> b \ ef): a -> Result[IoError, b] \ (ef - FileRead) + IO = x ->
        run {
            Ok(f(x))
        } with handler FileRead {
            def exists(filename, k) = {
                try {
                    k(Files.exists(Paths.get(filename), (...{}: Vector[LinkOption])))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isDirectory(filename, k) = {
                try {
                    k(Files.isDirectory(Paths.get(filename), (...{}: Vector[LinkOption])))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isRegularFile(filename, k) = {
                try {
                    k(Files.isRegularFile(Paths.get(filename), (...{}: Vector[LinkOption])))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isReadable(filename, k) = {
                try {
                    k(Files.isReadable(Paths.get(filename)))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isSymbolicLink(filename, k) = {
                try {
                    k(Files.isSymbolicLink(Paths.get(filename)))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isWritable(filename, k) = {
                try {
                    k(Files.isWritable(Paths.get(filename)))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def isExecutable(filename, k) = {
                try {
                    k(Files.isExecutable(Paths.get(filename)))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                }
            }

            def accessTime(filename, k) = {
                try {
                    k(fileAttributes(Paths.get(filename)).lastAccessTime().toMillis())
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def creationTime(filename, k) = {
                try {
                    k(fileAttributes(Paths.get(filename)).creationTime().toMillis())
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def modificationTime(filename, k) = {
                try {
                    k(fileAttributes(Paths.get(filename)).lastModifiedTime().toMillis())
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def size(filename, k) = {
                try {
                    k(Files.size(Paths.get(filename)))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def read(filename, k) = {
                try {
                    k(new JString(Files.readAllBytes(Paths.get(filename))))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def readLines(filename, k) = {
                try {
                    k(ToFlix.toFlix(Files.readAllLines(Paths.get(filename))))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def readBytes(filename, k) = {
                try {
                    k(Array.toVector(Files.readAllBytes(Paths.get(filename))))
                } catch {
                    case ex: InvalidPathException => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: IOException          => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }

            def list(filename, k) = {
                try {
                    // TODO: Use java.nio.file.Files.list when we have support for Java generics.
                    let file = new File(filename);
                    k(Array.toList(file.list()))
                } catch {
                    case ex: InvalidPathException  => Err(IoError(ErrorKind.InvalidPath, ex.getMessage()))
                    case ex: NotDirectoryException => Err(IoError(ErrorKind.NotDirectory, ex.getMessage()))
                    case ex: IOException           => Err(IoError(ErrorKind.Other, ex.getMessage()))
                }
            }
        }

    ///
    /// Runs the `FileRead` effect of the given function `f`.
    ///
    /// In other words, re-interprets the `FileRead` effect using the `IO` effect.
    ///
    pub def runWithIO(f: Unit -> a \ ef): Result[IoError, a] \ (ef - FileRead) + {IO} = handle(f)()

    ///
    /// Returns the attributes of the given file `f`.
    /// May throw `IOException` and `SecurityException`.
    ///
    def fileAttributes(path: Path): BasicFileAttributes \ IO =
        Files.readAttributes(
            path,
            // "[...] invoking this method with a type parameter of BasicFileAttributes.class will not throw UnsupportedOperationException."
            Class.forName("java.nio.file.attribute.BasicFileAttributes"),
            (...{}: Vector[LinkOption])
        )

}
