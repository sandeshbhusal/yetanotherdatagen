package edu.boisestate.datagen.rmi;

import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.server.UnicastRemoteObject;
import java.util.HashMap;

import edu.boisestate.datagen.reporting.Record;

public class DataPointServerImpl extends UnicastRemoteObject implements DataPointServer {
    HashMap<String, Record> dataPoints = new HashMap<String, Record>();

    public DataPointServerImpl() throws RemoteException {
        super();
    }

    @Override
    public void receiveDataPoint(String testcase, Record datapoint) throws RemoteException, NotBoundException {
        System.out.println("Received datapoint: " + datapoint + " from testcase " + testcase);
    }

    public void start() throws AlreadyBoundException {
        System.out.println("Starting DataPointServer");
        try {
            DataPointServerImpl server = new DataPointServerImpl();
            LocateRegistry.createRegistry(1099);
            LocateRegistry.getRegistry().bind("DataPointServer", server);
            System.out.println("DataPointServer bound");
        } catch (RemoteException e) {
            System.err.println("Failed to bind DataPointServer");
            e.printStackTrace();
        }
    }
}
