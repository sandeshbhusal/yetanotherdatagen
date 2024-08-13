package edu.boisestate.datagen.instrumenters;

/* Instrumentation modes:
 * - INSTRUMENTATION: instruments the code to report data points
 * - AUGMENTATION: augments the code to exclude seen variables
 */
public enum InstrumentationMode {
    INSTRUMENTATION, AUGMENTATION
}
