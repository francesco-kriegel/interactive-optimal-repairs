package de.tu_dresden.inf.lat
package protege_components

import org.protege.editor.core.ProtegeApplication
import org.protege.editor.core.ui.progress.BackgroundTask

import java.beans.PropertyChangeEvent
import javax.swing.SwingWorker

private abstract class ProtegeWorker[T, V] extends SwingWorker[T, V] with BackgroundTask {

  this.addPropertyChangeListener((evt: PropertyChangeEvent) => {
    if evt.getPropertyName eq "state" then
      evt.getNewValue.asInstanceOf[SwingWorker.StateValue] match
        case SwingWorker.StateValue.PENDING => // Do nothing.
        case SwingWorker.StateValue.STARTED => ProtegeApplication.getBackgroundTaskManager.startTask(this)
        case SwingWorker.StateValue.DONE => ProtegeApplication.getBackgroundTaskManager().endTask(this)
  })

  var message: String = ""

  override def toString: String = message

  def executeAndThen(code: T => Unit): Unit = {
    this.andThen(code)
    this.execute()
  }

  private def andThen(code: T => Unit): Unit = {
    this.addPropertyChangeListener((evt: PropertyChangeEvent) => {
      if !isCancelled then
        if evt.getPropertyName eq "state" then
          evt.getNewValue.asInstanceOf[SwingWorker.StateValue] match
            case SwingWorker.StateValue.DONE => code(this.get())
            case _ => // Do nothing.
    })
  }

  def executeAndThen(code: => Unit): Unit = {
    executeAndThen((_: T) => { code })
  }

  def inParallelWith[U](other: ProtegeWorker[U, Void]): ProtegeWorker[(T,U), Void] = {
    val _this = ProtegeWorker.this
    () => {
      _this.execute()
      other.execute()
      (_this.get(), other.get())
    }
  }

}

object ProtegeWorker {

  private val activeWorkers = collection.mutable.ListBuffer[ProtegeWorker[_, Void]]()

  private object nextInt {
    private[this] var n = 0
    def apply() = { n += 1; n }
  }

  def asynchronouslyInNewWorker[T](code: => T): ProtegeWorker[T, Void] =
    asynchronouslyInNewWorker("interactive-optimal-repair-worker-" + nextInt()) {
      code
    }

  def asynchronouslyInNewWorker[T](message: String)(code: => T): ProtegeWorker[T, Void] = {
    val worker: ProtegeWorker[T, Void] = () => { code }
    worker.message = message
    activeWorkers += worker
    worker.addPropertyChangeListener((evt: PropertyChangeEvent) => {
      if evt.getPropertyName eq "state" then
        if evt.getNewValue.asInstanceOf[SwingWorker.StateValue] eq SwingWorker.StateValue.DONE then
          activeWorkers.synchronized {
            activeWorkers -= worker
          }
    })
    worker
  }

  def cancelActiveWorkers(): Unit = {
    activeWorkers.foreach(_.cancel(true))
    activeWorkers.clear()
  }

}
