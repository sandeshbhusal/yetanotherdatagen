package edu.boisestate.datagen.rmi;

import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.server.UnicastRemoteObject;
import java.util.HashMap;

import edu.boisestate.datagen.reporting.Record;
import edu.boisestate.datagen.server.Cache;

public class DataPointServerImpl extends UnicastRemoteObject implements DataPointServer {
    HashMap<String, Record> dataPoints = new HashMap<String, Record>();

    public DataPointServerImpl() throws RemoteException {
        super();
    }

    @Override
    public void receiveDataPoint(String testcase, Record datapoint) throws RemoteException, NotBoundException {
        // Add the data point to the cache.
        System.out.println("Received data point: " + datapoint.toString());
        Cache.getInstance().addDataPoint(testcase, datapoint);
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
