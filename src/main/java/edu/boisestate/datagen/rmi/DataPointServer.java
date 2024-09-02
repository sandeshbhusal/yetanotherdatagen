package edu.boisestate.datagen.rmi;

import java.rmi.NotBoundException;
import java.rmi.Remote;
import java.rmi.RemoteException;

import edu.boisestate.datagen.reporting.InstrumentationRecord;

public interface DataPointServer extends Remote {
    public void receiveDataPoint(InstrumentationRecord record) throws RemoteException, NotBoundException;
}
