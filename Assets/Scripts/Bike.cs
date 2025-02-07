using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Tracing;
using Unity.Mathematics;
using UnityEngine;
using UnityEngine.Rendering.Universal;

public class Bike : MonoBehaviour
{
    private float phi=0f;
    private float delta=0f;
    private float phidot=0f;
    private float deltadot=0f;
    private float v=0f;
    private float psidot=0f;
    private float thetaB=0f;
    private float thetaR=0f;
    private float thetaF=0f;
	
    private bool _forward=false;
    private bool _backward=false;
    [SerializeField] private float _maxSpeed=3f;
    [SerializeField] private float forwardSpeedThreshold=2f;
    [SerializeField] private float backwardSpeedThreshold=-2.5f;
    [SerializeField] private float _acceleration=5f;
    [SerializeField] private float _rotationMaxSpeed=1f;
    private float _rotationTargetSpeed=0f;
    [SerializeField] private float _omegaPhi=3f;
    [SerializeField] private float _omegaDelta=3f;
    private float _pedalRatio=1f;

    [SerializeField] private Transform _rearWheelDummy;
    [SerializeField] private Transform _rearWheel;
    [SerializeField] private Transform _body;
    [SerializeField] private Transform _handle;
    [SerializeField] private Transform _frontWheel;
    [SerializeField] private Transform _crank;
    [SerializeField] private Transform _pedalLeft;
    [SerializeField] private Transform _pedalRight;
    [SerializeField] private Transform _cameraBase;
    private Transform _camera;
    [SerializeField] private bool _camerFollow=true;

    private float w=1.02f;
    private float c=0.08f;
    private float lmd=Mathf.PI*0.1f;
    private float rR=0.3f;
    private float mR=2f;
    private float IRxx=0.0603f;
    private float IRyy=0.12f;
    private float xB=0.3f;
    private float zB=-0.9f;
    private float mB=85f;
    private float IBxx=9.2f;
    private float IBxz=2.4f;
    private float IBzz=2.8f;
    // private float IByy=11f;
    private float xH=0.9f;
    private float zH=-0.7f;
    private float mH=4f;
    private float IHxx=0.05892f;
    private float IHxz=-0.00756f;
    private float IHzz=0.00708f;
    // private float IHyy=0.06f;
    private float rF=0.35f;
    private float mF=3f;
    private float IFxx=0.1405f;
    private float IFyy=0.28f;

    private float g;
    private float mu;
    private float A20g;
    private float A21g;
    private float A30g;
    private float A31g;
    private float A20v;
    private float A21v;
    private float A30v;
    private float A31v;
    private float A22;
    private float A23;
    private float A32;
    private float A33;
    private Rigidbody rb;
    private float M100;
    private float M101;
    private float M110;
    private float M111;
    private Vector3 _handleAxis;
	private float psidotRef=1f;
    [SerializeField] private float _maxInterval=0.2f;
    private float _timer=0f;
    private bool _pressLeft=false;
    // private bool _pressRight=false;
    private bool _pushing=false;
    private bool _brake=false;
	private float _middleForwardPhiRatio=0f;
	private float _middleBackwardPhiRatio=0f;

    void Awake()
    {
        float mT=mR+mB+mH+mF;
        float xT=(xB*mB+xH*mH+w*mF)/mT;
        float zT=(-rR*mR+zB*mB+zH*mH-rF*mF)/mT;
        float ITxx=IRxx+IBxx+IHxx+IFxx+mR*rR*rR+mB*zB*zB+mH*zH*zH+mF*rF*rF;
        float ITxz=IBxz+IHxz-mB*xB*zB-mH*xH*zH+mF*w*rF;
        float IRzz=IRxx;
        float IFzz=IFxx;
        float ITzz=IRzz+IBzz+IHzz+IFzz+mB*xB*xB+mH*xH*xH+mF*w*w;
        float mA=mH+mF;
        float xA=(xH*mH+w*mF)/mA;
        float zA=(zH*mH-rF*mF)/mA;
        float IAxx=IHxx+IFxx+mH*(zH-zA)*(zH-zA)+mF*(rF+zA)*(rF+zA);
        float IAxz=IHxz-mH*(xH-xA)*(zH-zA)+mF*(w-xA)*(rF+zA);
        float IAzz=IHzz+IFzz+mH*(xH-xA)*(xH-xA)+mF*(w-xA)*(w-xA);
        float muA=(xA-w-c)*Mathf.Cos(lmd)-zA*Mathf.Sin(lmd);
        float IALL=mA*muA*muA+IAxx*Mathf.Sin(lmd)*Mathf.Sin(lmd)+2*IAxz*Mathf.Sin(lmd)*Mathf.Cos(lmd)+IAzz*Mathf.Cos(lmd)*Mathf.Cos(lmd);
        float IALx=-mA*muA*zA+IAxx*Mathf.Sin(lmd)+IAxz*Mathf.Cos(lmd);
        float IALz=mA*muA*xA+IAxz*Mathf.Sin(lmd)+IAzz*Mathf.Cos(lmd);
        mu=Mathf.Cos(lmd)/w*c;
        float SR=IRyy/rR;
        float SF=IFyy/rF;
        float ST=SR+SF;
        float SA=mA*muA+mu*mT*xT;
        float M00=ITxx;
        float M01=IALx+mu*ITxz;
        float M10=M01;
        float M11=IALL+2*mu*IALz+mu*mu*ITzz;
        float K000=mT*zT;
        float K001=-SA;
        float K010=K001;
        float K011=-SA*Mathf.Sin(lmd);
        float K200=0;
        float K201=Mathf.Cos(lmd)/w*(ST-mT*zT);
        float K210=0;
        float K211=Mathf.Cos(lmd)/w*(SA+SF*Mathf.Sin(lmd));
        float C100=0;
        float C101=mu*ST+SF*Mathf.Cos(lmd)+Mathf.Cos(lmd)/w*ITxz-mu*mT*zT;
        float C110=-(mu*ST+SF*Mathf.Cos(lmd));
        float C111=Mathf.Cos(lmd)/w*IALz+mu*(SA+Mathf.Cos(lmd)/w*ITzz);
        float Mdet=M00*M11-M01*M10;
        M100=M11/Mdet;
        M101=-M01/Mdet;
        M110=-M10/Mdet;
        M111=M00/Mdet;
        g=-Physics.gravity.y;
        A20g=M100*K000+M101*K010;
        A21g=M100*K001+M101*K011;
        A30g=M110*K000+M111*K010;
        A31g=M110*K001+M111*K011;
        A20v=M100*K200+M101*K210;
        A21v=M100*K201+M101*K211;
        A30v=M110*K200+M111*K210;
        A31v=M110*K201+M111*K211;
        A22=M100*C100+M101*C110;
        A23=M100*C101+M101*C111;
        A32=M110*C100+M111*C110;
        A33=M110*C101+M111*C111;
        rb=GetComponent<Rigidbody>();
        rb.mass=1;
        _handleAxis=new Vector3(0,-Mathf.Cos(lmd),Mathf.Sin(lmd));
    }

    void Start()
    {
		_camera=Camera.main.transform;
        _middleForwardPhiRatio=StableRatio(forwardSpeedThreshold);
        _middleBackwardPhiRatio=StableRatio(backwardSpeedThreshold);        
    }

    void Update()
    {
        if(Input.GetKeyDown(KeyCode.W)) _forward=true;
        if(Input.GetKeyUp(KeyCode.W)) _forward=false;
        if(Input.GetKeyDown(KeyCode.S)) _backward=true;
        if(Input.GetKeyUp(KeyCode.S)) _backward=false;
        if(Input.GetKeyDown(KeyCode.D)) _rotationTargetSpeed=_rotationMaxSpeed;
        if(Input.GetKeyUp(KeyCode.D)) _rotationTargetSpeed=0;
        if(Input.GetKeyDown(KeyCode.A)) _rotationTargetSpeed=-_rotationMaxSpeed;
        if(Input.GetKeyUp(KeyCode.A)) _rotationTargetSpeed=0;
        if(_camerFollow)
        {
            _camera.position=_cameraBase.position;
            Vector3 cameraAngles=_camera.eulerAngles;
            Vector3 angles=transform.eulerAngles;
            _camera.rotation=Quaternion.Euler(cameraAngles.x,angles.y,cameraAngles.z);
        }
        if(Input.GetKeyDown(KeyCode.RightArrow) && _pressLeft) 
        {
            _pressLeft=false;
            _timer=0;
            _pushing=true;
        }
        // if(Input.GetKeyUp(KeyCode.RightArrow)) _pressRight=false;
        if(Input.GetKeyDown(KeyCode.LeftArrow) && !_pressLeft)
        {
            _pressLeft=true;
            _timer=0;
            _pushing=true;
        }
        // if(Input.GetKeyUp(KeyCode.LeftArrow)) _pressLeft=false;
        if(_pushing)
        {
            _timer+=Time.deltaTime;
            if(_timer>_maxInterval)
            {
                _timer=0;
                _pushing=false;
            }
        }
        if(Input.GetKeyDown(KeyCode.Space)) _brake=true;
        if(Input.GetKeyUp(KeyCode.Space)) _brake=false;
    }
    private float Kr0Fit(float v)
    {
        if(v>0) return -0.0181345f*v*v*v-0.4355809f*v*v+1.9299909f*v+31.7960207f-149.4310304f/Mathf.Max(v,forwardSpeedThreshold)-54.8453132f/(Mathf.Max(v,forwardSpeedThreshold)*Mathf.Max(v,forwardSpeedThreshold));
        else return -1.0982163f*v*v*v-26.5265293f*v*v-257.4888844f*v-1318.51725f-3700.7434108f/Mathf.Min(v,backwardSpeedThreshold)-4922.1099548f/(Mathf.Min(v,backwardSpeedThreshold)*Mathf.Min(v,backwardSpeedThreshold));
    }
    private float Kr1Fit(float v)
    {
        if(v>0) return 0.6490863f*v*v*v-7.7817937f*v*v+25.0574268f*v-1.2782334f-8.2878235f/Mathf.Max(v,forwardSpeedThreshold)+2.6855031f/(Mathf.Max(v,forwardSpeedThreshold)*Mathf.Max(v,forwardSpeedThreshold));
        else return 1.5477606f*v*v*v+33.4560748f*v*v+251.5365086f*v+855.7662461f+1240.4571693f/Mathf.Min(v,backwardSpeedThreshold)+992.8916209f/(Mathf.Min(v,backwardSpeedThreshold)*Mathf.Min(v,backwardSpeedThreshold));
    }
    private float Kr2Fit(float v)
    {
        if(v>0) return 0.1389298f*v*v*v-2.3482511f*v*v+12.1949568f*v-14.1203746f-24.2075703f/Mathf.Max(v,forwardSpeedThreshold)-26.232427f/(Mathf.Max(v,forwardSpeedThreshold)*Mathf.Max(v,forwardSpeedThreshold));
        else return -0.2728386f*v*v*v-6.4022505f*v*v-59.9339861f*v-322.8876835f-972.1211876f/Mathf.Min(v,backwardSpeedThreshold)-1404.7465192f/(Mathf.Min(v,backwardSpeedThreshold)*Mathf.Min(v,backwardSpeedThreshold));
    }
    private float Kr3Fit(float v)
    {
        if(v>0) return 0.0220897f*v*v*v-0.1309274f*v*v-0.9108832f*v+7.0379025f-4.4716835f/Mathf.Max(v,forwardSpeedThreshold)+0.9996634f/(Mathf.Max(v,forwardSpeedThreshold)*Mathf.Max(v,forwardSpeedThreshold));
        else return 0.0645608f*v*v*v+1.3736309f*v*v+9.094728f*v+33.4847332f+28.38103f/Mathf.Min(v,backwardSpeedThreshold)-10.13199f/(Mathf.Min(v,backwardSpeedThreshold)*Mathf.Min(v,backwardSpeedThreshold));
    }
    private float StableRatio(float v)
    {
        float Kr0=Kr0Fit(v);
        float Kr1=Kr1Fit(v);
        float C00=-g*A20g-v*v*A20v-M101*Kr0;
        float C01=-g*A21g-v*v*A21v-M101*Kr1;
        float C10=-g*A30g-v*v*A30v-M111*Kr0;
        float C11=-g*A31g-v*v*A31v-M111*Kr1;
        float Cdet=C00*C11-C01*C10;
        float C100=C11/Cdet;
        float C101=-C01/Cdet;
        float C110=-C10/Cdet;
        float C111=C00/Cdet;
        return (C100*M101+C101*M111)/(C110*M101+C111*M111); // phi/delta
    }
    void FixedUpdate()
    {
        Vector3 localVelocity=transform.InverseTransformDirection(rb.velocity);
        v=localVelocity.z;
		float verticalVelocity=localVelocity.y;
        if(_forward)
        {
		    if(v>(2*_maxSpeed)) v=2*_maxSpeed;
        }
        else
        {
            if(v>_maxSpeed) v=_maxSpeed;
            else if (v<-_maxSpeed) v=-_maxSpeed;
        }
		rb.velocity=transform.TransformDirection(new Vector3(0,verticalVelocity,v));
        var phidotTemp=phidot;
        var deltadotTemp=deltadot;
        if(backwardSpeedThreshold<v && v<forwardSpeedThreshold)
        {
			float deltaTarget;
			float phiTarget;
			if(v>0)
			{
				deltaTarget=-_rotationTargetSpeed/(Mathf.Cos(lmd)/w*forwardSpeedThreshold);
				phiTarget=deltaTarget*_middleForwardPhiRatio;
			}
			else
			{
				deltaTarget=_rotationTargetSpeed/(Mathf.Cos(lmd)/w*backwardSpeedThreshold);
				phiTarget=deltaTarget*_middleBackwardPhiRatio;
			}
            phidot+=Time.fixedDeltaTime*(-2*_omegaPhi*phidot-_omegaPhi*_omegaPhi*(phi-phiTarget));
            deltadot+=Time.fixedDeltaTime*(-2*_omegaDelta*deltadot-_omegaDelta*_omegaDelta*(delta-deltaTarget));
        }
        else
        {
			float Kr0=Kr0Fit(v);
			float Kr1=Kr1Fit(v);
			float Kr2=Kr2Fit(v);
			float Kr3=Kr3Fit(v);
			float C00=-g*A20g-v*v*A20v-M101*Kr0;
            float C01=-g*A21g-v*v*A21v-M101*Kr1;
            float C10=-g*A30g-v*v*A30v-M111*Kr0;
            float C11=-g*A31g-v*v*A31v-M111*Kr1;
            float Cdet=C00*C11-C01*C10;
            float C110=-C10/Cdet;
            float C111=C00/Cdet;
            psidotRef=Mathf.Cos(lmd)/w*v*(C110*M101+C111*M111);
			if(v<0) psidotRef*=-1;
            float tau=-Kr0*phi-Kr1*delta-Kr2*phidot-Kr3*deltadot+_rotationTargetSpeed/psidotRef;
            phidot+=Time.fixedDeltaTime*((-g*A20g-v*v*A20v)*phi+(-g*A21g-v*v*A21v)*delta-v*A22*phidot-v*A23*deltadot+M101*tau);
            deltadot+=Time.fixedDeltaTime*((-g*A30g-v*v*A30v)*phi+(-g*A31g-v*v*A31v)*delta-v*A32*phidot-v*A33*deltadot+M111*tau);
        }
        phi+=Time.fixedDeltaTime*phidotTemp;
        delta+=Time.fixedDeltaTime*deltadotTemp;
        psidot=Mathf.Cos(lmd)/w*(v*delta+c*deltadot);
        thetaB=-mu*(phi*delta+Mathf.Sin(lmd)*delta*delta/2);
        thetaR+=-Time.fixedDeltaTime*v/rR;
        thetaR%=2*Mathf.PI;
        thetaF+=-Time.fixedDeltaTime*v/rF;
        thetaF%=2*Mathf.PI;
        transform.Rotate(transform.up,-Time.fixedDeltaTime*psidot*180/Mathf.PI);
        _rearWheelDummy.localRotation=Quaternion.Euler(0,0,phi*180/Mathf.PI);
        _rearWheel.localRotation=Quaternion.Euler(0,0,phi*180/Mathf.PI)*Quaternion.Euler(-thetaR*180/Mathf.PI,0,0);
        _body.localRotation=Quaternion.Euler(thetaB*180/Mathf.PI,0,0);
        _handle.localRotation=Quaternion.AngleAxis(delta*180/Mathf.PI,_handleAxis);
        _frontWheel.localRotation=Quaternion.AngleAxis(delta*180/Mathf.PI,_handleAxis)*Quaternion.Euler(-thetaF*180/Mathf.PI,0,0);
		_crank.localRotation=Quaternion.Euler(-thetaR*180/Mathf.PI*_pedalRatio,0,0);
        _pedalLeft.localRotation=Quaternion.Euler(thetaR*180/Mathf.PI*_pedalRatio,0,0);
        _pedalRight.localRotation=Quaternion.Euler(thetaR*180/Mathf.PI*_pedalRatio,0,0);
        Vector3 angles=transform.eulerAngles;
        transform.rotation=Quaternion.Euler(angles.x,angles.y,0);
        // if(_forward) rb.AddForce(transform.forward*_acceleration);
        // if(_backward) rb.AddForce(-transform.forward*_acceleration);
        if(_pushing)
        {
            if(_backward)  rb.AddForce(-transform.forward*_acceleration);
            else if(_forward)  rb.AddForce(transform.forward*_acceleration*2);
            else rb.AddForce(transform.forward*_acceleration);
        }
        if(_brake)
        {
            if(v>0) rb.AddForce(-transform.forward*_acceleration);
            else rb.AddForce(transform.forward*_acceleration);
        }
    }
}
