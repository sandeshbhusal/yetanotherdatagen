package edu.boisestate.datagen.rmi;

import java.rmi.NotBoundException;
import java.rmi.Remote;
import java.rmi.RemoteException;

import edu.boisestate.datagen.reporting.Record;

public interface DataPointServer extends Remote {
    public void receiveDataPoint(String testcase,Record datapoint) throws RemoteException, NotBoundException;
}
